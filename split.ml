open Term
open Ident
open Task
open Decl

module M : sig
  type 'a t

  val empty : 'a t
  val singleton : 'a -> 'a t
  val union : 'a t -> 'a t -> 'a t
  val to_list : 'a t -> 'a list
end = struct
  type 'a t = Empty | Leaf of 'a | Node of 'a t * 'a t

  let empty = Empty
  let singleton elm = Leaf elm
  let union s1 s2 = Node (s1, s2)

  let to_list s =
    let acc = ref [] in
    let rec loop = function
      | Empty -> ()
      | Leaf a -> acc := a :: !acc
      | Node (s1, s2) ->
          loop s2;
          loop s1
    in
    loop s;
    !acc
end

let asym f = Sattr.mem asym_split f.t_attrs
let unasym f = Term.t_attr_remove asym_split f

type e_ret = { plus : term Lazy.t; minus : term Lazy.t }

type split_ret = {
  s_p : task -> task M.t;
  s_m : task -> task M.t;
  s_all : task -> task M.t;
}

let ( +++ ) a b = M.union a b
let vsymb_to_lsymb s = create_lsymbol (id_clone s.vs_name) [] (Some s.vs_ty)

let lvsymb_to_lsymb l =
  List.fold_left
    (fun (acc_symb, acc_term) x ->
      let new_lsymb = vsymb_to_lsymb x in
      (new_lsymb :: acc_symb, Mvs.add x (t_app_infer new_lsymb []) acc_term))
    ([], Mvs.empty) l

let context_add_hyp e t =
  Task.add_prop_decl t Paxiom
    (Decl.create_prsymbol (id_fresh "Hyp"))
    (Lazy.force e)

let context_add_lconst l g =
  List.fold_left (fun acc s -> Task.add_param_decl acc s) g l

let context_add_def s d g =
  let def = make_ls_defn s [] d in
  Task.add_logic_decl g [ def ]

let add_goal pr_symb t g =
  M.singleton (Task.add_prop_decl g Pgoal pr_symb (Lazy.force t))

let prsymb_build txt =
  let i = ref 1 in
  fun () ->
    let res = Decl.create_prsymbol (Ident.id_fresh (txt ^ string_of_int !i)) in
    incr i;
    res

let l_not a = Lazy.map t_not_simp a

let l_and, l_or, l_imp =
  let binop f a b = Lazy.from_val (f (Lazy.force a) (Lazy.force b)) in
  (binop t_and_simp, binop t_or_simp, binop t_implies_simp)

let rec e t =
  match t.t_node with
  | Ttrue | Tfalse | Tconst _ | Tvar _ | Tapp _ | Teps _ ->
      { plus = Lazy.from_val t; minus = Lazy.from_val t }
  (* ¬a *)
  | Tnot a ->
      let a = e a in
      { plus = l_not a.minus; minus = l_not a.plus }
  (* a so b *)
  | Tbinop (Tand, a, { t_node = Tbinop (Tor, b, { t_node = Ttrue; _ }); _ })
    when asym b ->
      let a = e a in
      let b = e b in
      { plus = a.plus; minus = l_and a.minus b.minus }
  (* a by b *)
  | Tbinop (Timplies, { t_node = Tbinop (Tor, b, { t_node = Ttrue; _ }); _ }, a)
    when asym b ->
      let a = e a in
      let b = e b in
      { plus = b.plus; minus = a.minus }
  (* a || b *)
  | Tbinop (Tor, a, b) when asym a ->
      let a = e a in
      let b = e b in
      {
        plus = l_or a.plus b.plus;
        minus = l_or a.minus (l_and (l_not a.plus) b.minus);
      }
  (* a && b *)
  | Tbinop (Tand, a, b) when asym a ->
      let a = e a in
      let b = e b in
      {
        plus = l_and a.plus (l_imp a.minus b.plus);
        minus = l_and a.minus b.minus;
      }
  (* a /\ b *)
  | Tbinop (Tand, a, b) ->
      let a = e a in
      let b = e b in
      { plus = l_and a.plus b.plus; minus = l_and a.minus b.minus }
  (* a \/ b *)
  | Tbinop (Tor, a, b) ->
      let a = e a in
      let b = e b in
      { plus = l_or a.plus b.plus; minus = l_or a.minus b.minus }
  (* a -> b *)
  | Tbinop (Timplies, a, b) ->
      let a = e a in
      let b = e b in
      { plus = l_imp a.minus b.plus; minus = l_or (l_not a.plus) b.minus }
  (* a <-> b *)
  | Tbinop (Tiff, a, b) ->
      let a = e a in
      let b = e b in
      {
        plus = l_and (l_imp a.minus b.plus) (l_imp b.minus a.plus);
        minus =
          l_or (l_and a.minus b.minus) (l_and (l_not a.plus) (l_not b.plus));
      }
  (* ∀x. b *)
  | Tquant (Tforall, a) ->
      let cq, a =
        let vl, tl, a, close = t_open_quant_cb a in
        ((fun x -> t_forall (close vl tl x)), a)
      in
      let a = e a in
      { plus = Lazy.map cq a.plus; minus = Lazy.map cq a.minus }
  (* ∃x. b *)
  | Tquant (Texists, a) ->
      let cq, a =
        let vl, tl, a, close = t_open_quant_cb a in
        ((fun x -> t_exists (close vl tl x)), a)
      in
      let a = e a in
      { plus = Lazy.map cq a.plus; minus = Lazy.map cq a.minus }
  (* let c = b in a *)
  | Tlet (b, bound) ->
      let c, a, close = t_open_bound_cb bound in
      let a = e a in
      let plus =
        lazy
          (t_forall_close [ c ] []
             (t_implies (t_equ (t_var c) b) (Lazy.force a.plus)))
      in
      let minus = lazy (t_let_simp b (close c (Lazy.force a.minus))) in
      { plus; minus }
  (* if a then b else c *)
  | Tif (a, b, c) ->
      let a = e a in
      let b = e b in
      let c = e c in
      let nap = l_not a.plus in
      {
        plus = l_and (l_imp a.minus b.plus) (l_imp nap c.plus);
        minus = l_or (l_and a.minus b.minus) (l_and nap c.minus);
      }
  (* match e with c *)
  | Tcase _ -> assert false

let split = function
  | None -> []
  | Some task_hd as task ->
      let pr_symb = task_goal task in
      let so_prsymb = prsymb_build (pr_symb.pr_name.id_string ^ "_so_sc_") in
      let by_prsymb = prsymb_build (pr_symb.pr_name.id_string ^ "_by_sc_") in
      let rec split t =
        match t.t_node with
        (* Atomic cases *)
        | Ttrue ->
            let s_p _ = M.empty in
            let s_m g =
              M.singleton (Task.add_prop_decl g Pgoal pr_symb t_false)
            in
            let s_all _ = M.empty in
            { s_p; s_m; s_all }
        | Tfalse ->
            let s_p g = M.singleton (Task.add_prop_decl g Pgoal pr_symb t) in
            let s_m _ = M.empty in
            let s_all _ = M.empty in
            { s_p; s_m; s_all }
        | Tconst _ | Tvar _ | Tapp _ | Teps _ ->
            let s_p g = M.singleton (Task.add_prop_decl g Pgoal pr_symb t) in
            let s_m g =
              M.singleton (Task.add_prop_decl g Pgoal pr_symb (t_not_simp t))
            in
            let s_all _ = M.empty in
            { s_p; s_m; s_all }
        (* ¬a *)
        | Tnot a ->
            let sa = split a in
            let s_p = sa.s_m in
            let s_m = sa.s_p in
            let s_all = sa.s_all in
            { s_p; s_m; s_all }
        (* a so b *)
        | Tbinop
            (Tand, a, { t_node = Tbinop (Tor, b, { t_node = Ttrue; _ }); _ })
          when asym b ->
            let sa = split a in
            let sb = split (unasym b) in
            let a = e a in
            let b = e b in
            let s_p g =
              let g2 = context_add_hyp a.minus g in
              sa.s_p g +++ sb.s_p g2
            in
            let s_m g =
              let g2 = context_add_hyp a.minus g in
              sa.s_all g +++ sb.s_p g2
              +++ add_goal (so_prsymb ()) (l_not b.minus) g2
            in
            let s_all g =
              let g2 = context_add_hyp a.minus g in
              sa.s_all g +++ sb.s_p g2
            in
            { s_p; s_m; s_all }
        (* a by b *)
        | Tbinop
            (Timplies, { t_node = Tbinop (Tor, b, { t_node = Ttrue; _ }); _ }, a)
          when asym b ->
            let sa = split a in
            let sb = split (unasym b) in
            let a = e a in
            let b = e b in
            let s_p g =
              sb.s_p g +++ sa.s_all g
              +++ add_goal (by_prsymb ()) a.plus (context_add_hyp b.minus g)
            in
            let s_m g =
              sb.s_all g +++ sa.s_m g
              +++ add_goal (by_prsymb ()) a.plus (context_add_hyp b.minus g)
            in
            let s_all g =
              sb.s_all g +++ sa.s_all g
              +++ add_goal (by_prsymb ()) a.plus (context_add_hyp b.minus g)
            in
            { s_p; s_m; s_all }
        (* a || b *)
        | Tbinop (Tor, a, b) when asym a ->
            let sa = split (unasym a) in
            let sb = split b in
            let a = e a in
            let s_p g =
              sa.s_all g +++ sb.s_p (context_add_hyp (l_not a.plus) g)
            in
            let s_m g =
              sa.s_m g +++ sb.s_m (context_add_hyp (l_not a.plus) g)
            in
            let s_all g =
              sa.s_all g +++ sb.s_all (context_add_hyp (l_not a.plus) g)
            in
            { s_p; s_m; s_all }
        (* a && b *)
        | Tbinop (Tand, a, b) when asym a ->
            let sa = split (unasym a) in
            let sb = split b in
            let a = e a in
            let s_p g = sa.s_p g +++ sb.s_p (context_add_hyp a.minus g) in
            let s_m g = sa.s_all g +++ sb.s_m (context_add_hyp a.minus g) in
            let s_all g = sa.s_all g +++ sb.s_all (context_add_hyp a.minus g) in
            { s_p; s_m; s_all }
        (* a /\ b *)
        | Tbinop (Tand, a, b) ->
            let sa = split a in
            let sb = split b in
            let a = e a in
            let s_p g = sa.s_p g +++ sb.s_p g in
            let s_m g = sa.s_all g +++ sb.s_m (context_add_hyp a.minus g) in
            let s_all g = sa.s_all g +++ sb.s_all g in
            { s_p; s_m; s_all }
        (* a \/ b *)
        | Tbinop (Tor, a, b) ->
            let sa = split a in
            let sb = split b in
            let a = e a in
            let s_p g =
              sa.s_all g +++ sb.s_p (context_add_hyp (l_not a.plus) g)
            in
            let s_m g = sa.s_m g +++ sb.s_m g in
            let s_all g =
              sa.s_all g +++ sb.s_all (context_add_hyp (l_not a.plus) g)
            in
            { s_p; s_m; s_all }
        (* a -> b *)
        | Tbinop (Timplies, a, b) ->
            let sa = split a in
            let sb = split b in
            let a = e a in
            let s_p g = sa.s_all g +++ sb.s_p (context_add_hyp a.minus g) in
            let s_m g = sa.s_p g +++ sb.s_m g in
            let s_all g = sa.s_all g +++ sb.s_all (context_add_hyp a.minus g) in
            { s_p; s_m; s_all }
        (* a <-> b *)
        | Tbinop (Tiff, a, b) ->
            let sa = split a in
            let sb = split b in
            let a = e a in
            let b = e b in
            let s_p g =
              sa.s_all g +++ sb.s_all g
              +++ sb.s_p (context_add_hyp a.minus g)
              +++ sa.s_p (context_add_hyp b.minus g)
            in
            let s_m g =
              sa.s_all g
              +++ sb.s_m (context_add_hyp a.minus g)
              +++ sb.s_p (context_add_hyp (l_not a.plus) g)
            in
            let s_all g =
              sa.s_all g +++ sb.s_all g
              +++ sb.s_all (context_add_hyp a.minus g)
              +++ sa.s_all (context_add_hyp b.minus g)
            in
            { s_p; s_m; s_all }
        (* ∀x. b *)
        | Tquant (Tforall, a) ->
            let vl, tl, a = t_open_quant a in
            let new_symb, term_map = lvsymb_to_lsymb vl in
            let sa, a = (split (t_subst term_map a), e a) in
            let s_p g =
              let g2 = context_add_lconst new_symb g in
              sa.s_p g2
            in
            let s_m g =
              let g2 = context_add_lconst new_symb g in
              let goal_t =
                Lazy.map (fun x -> t_exists_close vl tl (t_not_simp x)) a.plus
              in
              sa.s_all g2 +++ add_goal pr_symb goal_t g
            in
            let s_all g =
              let g2 = context_add_lconst new_symb g in
              sa.s_all g2
            in
            { s_p; s_m; s_all }
        (* ∃x. b *)
        | Tquant (Texists, a) ->
            let vl, tl, a = t_open_quant a in
            let new_symb, term_map = lvsymb_to_lsymb vl in
            let sa, a = (split (t_subst term_map a), e a) in
            let s_p g =
              let g2 = context_add_lconst new_symb g in
              let goal_t = Lazy.map (fun x -> t_exists_close vl tl x) a.plus in
              sa.s_all g2 +++ add_goal pr_symb goal_t g
            in
            let s_m g =
              let g2 = context_add_lconst new_symb g in
              sa.s_p g2
            in

            let s_all g =
              let g2 = context_add_lconst new_symb g in
              sa.s_all g2
            in
            { s_p; s_m; s_all }
        (* let c = b in a *)
        | Tlet (b, bound) ->
            let c, a = t_open_bound bound in
            let new_symb = vsymb_to_lsymb c in
            let sa = split (t_subst_single c (t_app_infer new_symb []) a) in
            let s_p g =
              let g2 = context_add_def new_symb b g in
              sa.s_p g2
            in
            let s_m g =
              let g2 = context_add_def new_symb b g in
              sa.s_m g2
            in
            let s_all g =
              let g2 = context_add_def new_symb b g in
              sa.s_all g2
            in
            { s_p; s_m; s_all }
        (* if a then b else c *)
        | Tif (a, b, c) ->
            let sa = split a in
            let sb = split b in
            let sc = split c in
            let a = e a in
            let s_p g =
              sa.s_all g
              +++ sb.s_p (context_add_hyp a.minus g)
              +++ sc.s_p (context_add_hyp (l_not a.plus) g)
            in
            let s_m g =
              sa.s_all g
              +++ sb.s_m (context_add_hyp a.minus g)
              +++ sc.s_m (context_add_hyp (l_not a.plus) g)
            in
            let s_all g =
              sa.s_all g
              +++ sb.s_all (context_add_hyp a.minus g)
              +++ sc.s_all (context_add_hyp (l_not a.plus) g)
            in
            { s_p; s_m; s_all }
        (* match e with c *)
        | Tcase _ -> assert false
      in
      let term = task_goal_fmla task in
      let s = split term in
      let goal_list = M.to_list (s.s_p task_hd.task_prev) in
      goal_list

let split = Trans.store split

let () =
  Trans.register_transform_l "ninja" split
    ~desc:"Split@ your@ formulas@ like@ a@ Nijaaaa."
