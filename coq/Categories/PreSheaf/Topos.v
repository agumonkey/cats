Require Import Category.Main.
Require Import Topos.Topos.
Require Import Limits.Limit.
Require Import Coq_Cats.Type_Cat.Card_Restriction.
Require Import PreSheaf.PreSheaf.
Require Import PreSheaf.CCC.
Require Import PreSheaf.Complete.
Require Import PreSheaf.SubObject_Classifier. 

Instance Type_Cat_Topos (C : Category) : Topos :=
  {
    Topos_Cat := PShCat C;
    Topos_Cat_CCC := PShCat_CCC C;
    Topos_Cat_SOC := PSh_SubObject_Classifier C;
    Topos_Cat_Fin_Limit := Complete_Has_Restricted_Limits (PShCat C) Finite
  }.