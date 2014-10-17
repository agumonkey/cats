Require Import Category.Main.
Require Import Basic_Cons.Initial.
Require Import Essentials.Empty.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

Program Instance Empty_init : Initial Type_Cat Empty.

(* Empty_init Proved! *)

Program Instance Type_Cat_Has_Initial : Has_Initial Type_Cat :=
{
  HI_init := Empty
}.

(* Type_Cat_Has_Initial Proved! *)

