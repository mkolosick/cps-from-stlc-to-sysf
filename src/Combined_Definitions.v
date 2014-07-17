(***************************************************************************
* STLC (combined language) definitions From Ahmed & Blume ICFP 2011       *
* Matthew Kolosick                                                        *
***************************************************************************)

Require Import Core_Definitions LibWfenv Source_Definitions Target_Definitions Cps_Trans.

(* ********************************************************************** *)

Inductive st_type : typ -> Prop :=
  | st_s_type : forall s, s_type s -> st_type s
  | st_t_type : forall t, t_type t -> st_type t.

Hint Constructors st_type.

Inductive st_s_term : trm -> Prop :=
  | st_s_term_value : forall v, st_s_value v -> st_s_term v
  | st_s_term_if : forall e1 e2 e3,
      st_s_term e1 -> st_s_term e2 -> st_s_term e3 ->
      st_s_term (s_trm_if e1 e2 e3)
  | st_s_term_app : forall e1 e2,
      st_s_term e1 -> st_s_term e2 ->
      st_s_term (s_trm_app e1 e2)
  | st_s_term_st : forall e s,
      st_t_term e -> s_type s ->
      st_s_term (s_trm_st e s)

with st_s_value : trm -> Prop :=
  | st_s_value_var :  forall x, st_s_value (s_trm_fvar x)
  | st_s_value_true : st_s_value s_trm_true
  | st_s_value_false : st_s_value s_trm_false
  | st_s_value_abs : forall L s e,
      (forall x, x \notin L -> st_s_term (s_open_ee_var e x)) ->
      (s_type s) ->
      st_s_value (s_trm_abs s e)

with st_t_term : trm -> Prop :=
  | st_t_term_value : forall u, st_t_value u -> st_t_term u
  | st_t_term_if : forall u m1 m2,
      st_t_value u -> st_t_term m1 -> st_t_term m2 -> st_t_term (t_trm_if u m1 m2)
  | st_t_term_let_fst : forall L u m,
      st_t_value u ->
      (forall x, x \notin L -> st_t_term (t_open_ee_var m x)) ->
      st_t_term (t_trm_let_fst u m)
  | st_t_term_let_snd : forall L u m,
      st_t_value u ->
      (forall x, x \notin L -> st_t_term (t_open_ee_var m x)) ->
      st_t_term (t_trm_let_snd u m)
  | st_t_term_app : forall u1 t u2,
      st_t_value u1 -> t_type t -> st_t_value u2 -> st_t_term (t_trm_app u1 t u2)
  | st_t_term_ts : forall e s m,
      st_s_term e -> s_type s -> st_t_term m -> st_t_term (t_trm_ts e s m)

with st_t_value : trm -> Prop :=
  | st_t_value_var : forall x, st_t_value (t_trm_fvar x)
  | st_t_value_true : st_t_value t_trm_true
  | st_t_value_false : st_t_value t_trm_false
  | st_t_value_pair : forall u1 u2,
      st_t_value u1 -> st_t_value u2 -> st_t_value (t_trm_pair u1 u2)
  | t_value_abs : forall L t m,
      (forall X, X \notin L -> t_type (open_tt_var t X)) ->
      (forall x X, x \notin L -> X \notin L ->
        st_t_term (open_te_var (t_open_ee_var m x) X)) ->
      st_t_value (t_trm_abs t m).

Scheme st_s_term_mut := Induction for st_s_term Sort Prop
with st_s_value_mut := Induction for st_s_value Sort Prop
with st_t_term_mut := Induction for st_t_term Sort Prop
with st_t_value_mut := Induction for st_t_value Sort Prop.

Hint Constructors st_s_term st_s_value st_t_term st_t_value.

Inductive st_term : trm -> Prop :=
  | st_source_term : forall e, st_s_term e -> st_term e
  | st_target_term : forall e, st_t_term e -> st_term e

with st_value : trm -> Prop :=
  | st_source_value : forall v, st_s_value v -> st_value v
  | st_target_value : forall v, st_t_value v -> st_value v.

Scheme st_term_mut := Induction for st_term Sort Prop
with st_value_mut := Induction for st_value Sort Prop.

Hint Constructors st_term st_value.

Inductive st_wft : env_type -> typ -> Prop :=
  | st_s_wft_bool : forall D, ok D -> st_wft D s_typ_bool
  | st_s_wft_arrow : forall D t1 t2,
      st_wft D t1 -> st_wft D t2 -> st_wft D (s_typ_arrow t1 t2)
  | st_t_wft_var : forall D X, ok D -> binds X star D -> st_wft D (t_typ_fvar X)
  | st_t_wft_bool : forall D, ok D -> st_wft D t_typ_bool
  | st_t_wft_pair : forall D t1 t2,
      st_wft D t1 -> st_wft D t2 -> st_wft D (t_typ_pair t1 t2)
  | st_t_wft_arrow : forall L D t1 t2,
      (forall X, X \notin L -> st_wft (D & X ~ star) (open_tt_var t1 X)) ->
      (forall X, X \notin L -> st_wft (D & X ~ star) (open_tt_var t2 X)) ->
      st_wft D (t_typ_arrow t1 t2).

Hint Constructors st_wft.

(* Still need the boundary term typing rules *)
Inductive st_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | st_typing_s : forall D G u t,
      st_s_typing D G u t -> st_typing D G u t
  | st_typing_t : forall D G u t,
      st_t_typing D G u t -> st_typing D G u t
  | st_typing_st : forall D G e s,
      st_t_typing D G e (cps_type_trans s) ->
      st_typing D G (s_trm_st e s) s
  | st_typing_ts : forall L D G e1 e2 s t,
      st_s_typing D G e1 s ->
      (forall x, x \notin L -> st_t_typing D (G & x ~ (cps_type_trans s)) (t_open_ee_var e2 x) t) ->
      st_typing D G (t_trm_ts e1 s e2) t

with st_s_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | st_s_typing_var : forall D G x t,
      ok D -> wfenv (st_wft D) G -> binds x t G ->
      st_s_typing D G (s_trm_fvar x) t
  | st_s_typing_true : forall D G,
      ok D -> wfenv (st_wft D) G -> st_s_typing D G s_trm_true s_typ_bool
  | st_s_typing_false : forall D G,
      ok D -> wfenv (st_wft D) G -> st_s_typing D G s_trm_false s_typ_bool
  | st_s_typing_abs : forall L D G e s1 s2,
      wfenv (st_wft D) G ->
      (forall x, x \notin L -> st_typing D (G & x ~ s1) (s_open_ee_var e x) s2) ->
      (st_type s1) ->
      st_s_typing D G (s_trm_abs s1 e) (s_typ_arrow s1 s2)
  | st_s_typing_if : forall D G e1 e2 e3 s,
      st_s_typing D G e1 s_typ_bool -> st_s_typing D G e2 s -> st_s_typing D G e3 s ->
      st_s_typing D G (s_trm_if e1 e2 e3) s
  | st_s_typing_app : forall D G e1 e2 s1 s2,
      st_s_typing D G e1 (s_typ_arrow s1 s2) -> st_s_typing D G e2 s1 ->
      st_s_typing D G (s_trm_app e1 e2) s2

with st_t_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | st_t_typing_value : forall D G u t,
      st_t_value_typing D G u t -> st_t_typing D G u t
  | st_t_typing_if : forall D G u m1 m2 t,
      st_t_value_typing D G u t_typ_bool ->
      st_t_typing D G m1 t -> st_t_typing D G m2 t ->
      st_t_typing D G (t_trm_if u m1 m2) t
  | st_t_typing_let_fst : forall L D G u m t1 t2 t,
      st_t_value_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notin L -> st_t_typing D (G & x ~ t1) (t_open_ee_var m x) t) ->
      st_t_typing D G (t_trm_let_fst u m) t
  | st_t_typing_let_snd : forall L D G u m t1 t2 t,
      st_t_value_typing D G u (t_typ_pair t1 t2) -> (forall x, x \notin L -> st_t_typing D (G & x ~ t2) (t_open_ee_var m x) t) -> st_t_typing D G (t_trm_let_snd u m) t
  | st_t_typing_app : forall D G u1 u2 t t1 t2,
      st_t_value_typing D G u1 (t_typ_arrow t1 t2) ->
      st_wft D t ->
      st_t_value_typing D G u2 (open_tt t1 t) ->
      st_t_typing D G (t_trm_app u1 t u2) (open_tt t2 t)

with st_t_value_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | st_t_value_typing_var : forall D G x t,
      ok D -> wfenv (st_wft D) G -> binds x t G ->
      st_t_value_typing D G (t_trm_fvar x) t
  | st_t_value_typing_true : forall D G,
      ok D -> wfenv (st_wft D) G -> st_t_value_typing D G t_trm_true t_typ_bool
  | st_t_value_typing_false : forall D G,
      ok D -> wfenv (st_wft D) G -> st_t_value_typing D G t_trm_false t_typ_bool
  | st_t_value_typing_pair : forall D G u1 u2 t1 t2,
      st_t_value_typing D G u1 t1 -> st_t_value_typing D G u2 t2 ->
      st_t_value_typing D G (t_trm_pair u1 u2) (t_typ_pair t1 t2)
  | st_t_value_typing_abs : forall L D G m t1 t2,
      wfenv (st_wft D) G ->
      (forall x X, x \notin L -> X \notin L ->
        st_t_typing (D & X ~ star)
                    (G & x ~ (open_tt_var t1 X))
                    (open_te_var (t_open_ee_var m x) X)
                    (open_tt_var t2 X)) ->
      st_t_value_typing D G (t_trm_abs t1 m) (t_typ_arrow t1 t2).