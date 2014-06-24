(***************************************************************************
* STLC (combined language) definitions From Ahmed & Blume ICFP 2011       *
* Matthew Kolosick                                                        *
***************************************************************************)

Require Import Core_Definitions LibWfenv Source_Definitions Target_Definitions.

(* ********************************************************************** *)

(* Combined Language Types *)

Inductive st_type : typ -> Prop :=
  | st_type_s_bool : st_type s_typ_bool
  | st_type_s_arrow : forall s1 s2,
      s_type s1 -> s_type s2 -> st_type (s_typ_arrow s1 s2)
  | st_type_t_var : forall x, st_type (t_typ_fvar x)
  | st_type_t_bool : st_type t_typ_bool
  | st_type_t_pair : forall t1 t2, 
      t_type t1 -> t_type t2 -> st_type (t_typ_pair t1 t2)
  | st_type_t_arrow : forall L t1 t2,
      (forall X, X \notin L -> t_type (open_tt_var t1 X)) ->
      (forall X, X \notin L -> t_type (open_tt_var t2 X)) ->
      st_type (t_typ_arrow t1 t2).

