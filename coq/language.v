Require Import Coq.Lists.List.
Import ListNotations.

Class component_language (component: Type) (program: Type): Type :=
  {
    compatible: list component -> Prop;
    complete: program -> Prop;

    link: list component -> program;

    beh_eq: program -> program -> Prop;

    beh_eq_refl: forall P, complete P -> beh_eq P P;
    beh_eq_sym: forall P Q,
                  complete P -> complete Q ->
                  beh_eq P Q ->
                  beh_eq Q P;
    beh_eq_trans: forall P Q R,
                    complete P -> complete Q -> complete R ->
                    beh_eq P Q -> beh_eq Q R ->
                    beh_eq P R
  }.
