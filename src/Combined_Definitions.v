(***************************************************************************
* STLC (combined language) definitions From Ahmed & Blume ICFP 2011       *
* Matthew Kolosick                                                        *
***************************************************************************)

Require Import Core_Definitions LibWfenv Source_Definitions Target_Definitions.

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

      