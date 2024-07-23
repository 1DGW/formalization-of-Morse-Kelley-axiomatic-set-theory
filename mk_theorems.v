(******************************************************************************)
(*          This project is distributed under the terms of the                *)
(*            GNU Lesser General Public License version 2.1                   *)
(*                (see file LICENSE for more details).                        *)
(*     It is developmented in the CoqIDE (version 8.13.2) for windows.        *)
(*                                                                            *)
(*                       This project is implemented by                       *)
(*                Wensheng Yu, Tianyu sun, Yaoshun Fu, Dakai Guo,             *)
(*                    Si Chen, Qimeng Zhang and Guowei Dou                    *)
(*                                                                            *)
(*   Beijing Key Laboratory of Space-ground Interconnection and Convergence,  *)
(*                     School of Electronic Engineering,                      *)
(*        Beijing University of Posts and Telecommunications, Beijing         *)
(******************************************************************************)
(*           This file presents the formal verification of theorems           *)
(*                of Morse-Kelley (MK) axiomatic set theory.                  *)
(******************************************************************************)

(** mk_theorems *)

Require Export mk_structure.

(* Theo4  z∈x∪y iff z∈x or z∈y; z∈x∩y iff z∈x and z∈y *)
Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Ltac deHun :=
  match goal with
   | H:  ?c ∈ ?a∪?b
     |- _ => apply MKT4 in H as [] ; deHun
   | _ => idtac
  end.

Ltac deGun :=
  match goal with
    | |-  ?c ∈ ?a∪?b => apply MKT4 ; deGun
    | _ => idtac
  end.

Ltac deHin :=
  match goal with
   | H:  ?c ∈ ?a∩?b
     |- _ => apply MKT4' in H as []; deHin
   | _ => idtac  
  end.

Ltac deGin :=
  match goal with
    | |- ?c ∈ ?a∩?b => apply MKT4'; split; deGin
    | _ => idtac
  end.

(* Theo5  x∪x=x and x∩x=x *)
Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros; eqext; deGun; deHun; auto.
Qed.

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* Theo6  x∪y=y∪x and x∩y=y∩x *)
Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros; eqext; deHun; deGun; auto.
Qed.

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* Theo7  (x∪y)∪z=x∪(y∪z) and (x∩y)∩z=x∩(y∩z) *)
Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; eqext; deHun; deGun; auto;
  [right|right|left|left]; deGun; auto.
Qed.

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; eqext; deGin; deHin; auto.
Qed.

(* Theo8  x∩(y∪z)=(x∩y)∪(x∩z) and x∪(y∩z)=(x∪y)∩(x∪z) *)
Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; eqext; deHin; deHun; deGun; deGin; [left|right|..];
  deHin; deHun; deGun; deGin; auto.
Qed.

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; eqext; deHin; deHun; deGin; repeat deGun; deHin; auto.
  right; deGin; auto.
Qed.

(* Theo11  ¬ (¬ x) = x *)
Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros; eqext.
  - appA2H H. Absurd. elim H0. appA2G.
  - appA2G. intro. appA2H H0; auto.
Qed.

(* Theo12  De Morgan   ¬(x∪y)=(¬x)∩(¬y) and ¬(x∩y)=(¬x)∪(¬y) *)
Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; eqext.
  - appA2H H; deGin; appA2G; intro; apply H0; deGun; auto.
  - deHin. appA2H H; appA2H H0. appA2G. intro. deHun; auto.
Qed.

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros. rewrite <-(MKT11 x),<-(MKT11 y),<-MKT12.
  repeat rewrite MKT11; auto.
Qed.

Fact setminP : ∀ z x y, z ∈ x -> ~ z ∈ y -> z ∈ (x ~ y).
Proof.
  intros. appA2G. split; auto. appA2G.
Qed.

Global Hint Resolve setminP : core.

Fact setminp : ∀ z x y, z ∈ (x ~ y) -> z ∈ x /\ ~ z ∈ y.
Proof.
  intros. appA2H H. destruct H0. appA2H H1; auto.
Qed.

(* Theo14  x∩(y ~ z)=(x∩y) ~ z *)
Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Setminus; rewrite MKT7'; auto.
Qed.

(* Theo16  x∉Φ *)
Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros; intro. apply AxiomII in H; destruct H; auto.
Qed.

Ltac emf :=
  match goal with
    H:  ?a ∈ Φ
    |- _ => destruct (MKT16 H)
  end.

Ltac eqE := eqext; try emf; auto.

Ltac feine z := destruct (@ MKT16 z).

(* Theo17  Φ∪x=x and Φ∩x=Φ *)
Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros; eqext; deHun; deGun; auto; emf.
Qed.

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros. eqE. deHin; auto.
Qed.

(* Theo19  x∈μ iff x is a set  *)
Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  split; intros; eauto. appA2G.
Qed.

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros. apply MKT19; auto.
Qed.

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros. apply MKT19; auto.
Qed.

Global Hint Resolve MKT19a MKT19b : core.

(* Theo20  x∪μ=μ and x∩μ=x *)
Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros; eqext; deHun; deGun; eauto.
Qed.

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros; eqext; deHin; deGin; eauto.
Qed.

(* Theo21  ¬Φ=μ and ¬μ=Φ *)
Theorem MKT21 : ¬ Φ = μ.
Proof.
  eqext; appA2G. apply MKT16.
Qed.

Theorem MKT21' : ¬ μ = Φ.
Proof.
  rewrite <-MKT11,MKT21; auto.
Qed.

Ltac deHex1 :=
  match goal with
    H: ∃ x, ?P 
    |- _ => destruct H as []
  end.

Ltac rdeHex := repeat deHex1; deand.

(* Theo24  ∩Φ=μ and ∪Φ=Φ *)
Theorem MKT24 : ∩Φ = μ.
Proof.
  eqext; appA2G; intros; emf.
Qed.

Theorem MKT24' : ∪Φ = Φ.
Proof.
  eqE. appA2H H. rdeHex. emf.
Qed.

(* Theo26  Φ⊂x and x⊂μ *)
Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  unfold Included; intros; emf.
Qed.

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  unfold Included; intros; eauto.
Qed.

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  unfold Included; intros; auto.
Qed.

Global Hint Resolve MKT26 MKT26' MKT26a : core.

Fact ssubs : ∀ {a b z}, z ⊂ (a ~ b) -> z ⊂ a.
Proof.
  unfold Included; intros. apply H in H0. appA2H H0; tauto.
Qed.

Global Hint Immediate ssubs : core.

Fact esube : ∀ {z}, z ⊂ Φ -> z = Φ.
Proof. intros. eqE. Qed.

(* Theo27  x=y iff x⊂y and y⊂x *)
Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  split; intros; subst; [destruct H; eqext|split]; auto.
Qed.

(* Theo28  if x⊂y and y⊂z, then x⊂z *)
Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  unfold Included; intros; auto.
Qed.

(* Theo29  x⊂y iff x∪y=y *)
Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H; deGun|eqext; deGun; deHun]; auto.
Qed.

(* Theo30  x⊂y iff x∩y=x *)
Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H in H0; deHin|eqext; deGin; deHin]; auto.
Qed.

(* Theo31  if x⊂y, then ∪x⊂∪y and ∩y⊂∩x *)
Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  split; red; intros; appA2H H0; rdeHex; appA2G.
Qed.

(* Theo32  if x∈y, then x⊂∪y and ∩y⊂x *)
Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  split; red; intros; [appA2G|appA2H H0; auto].
Qed.

(* Theo33  if x is a set and z⊂x, then z is a set *)
Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. destruct (AxiomIII H) as [y []]; eauto.
Qed.

(* Theo34  0=∩μ and ∪μ =μ *)
Theorem MKT34 : Φ = ∩μ.
Proof.
  eqE. appA2H H. apply H0. appA2G. eapply MKT33; eauto.
Qed.

Theorem MKT34' : μ = ∪μ.
Proof.
  eqext; eauto. destruct (@ AxiomIII z) as [y []]; eauto. appA2G.
Qed.

(* Theo35  if x≠0, then ∩x is a set *)
Lemma NEexE : ∀ x, x ≠ Φ <-> ∃ z, z∈x.
Proof.
  split; intros.
  - Absurd. elim H; eqext; try emf. elim H0; eauto.
  - intro; subst. destruct H. emf.
Qed.

Ltac NEele H := apply NEexE in H as [].

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros. NEele H. eapply MKT33; eauto. apply MKT32; auto.
Qed.

(* Theo37  u=pow(u) *)
Theorem MKT37 : μ = pow(μ).
Proof.
  eqext; appA2G; eauto.
Qed.

(* Theo38  if x is a set, then pow(x) is a set *)
Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros. New (AxiomIII H). rdeHex. eapply MKT33; eauto.
  red; intros. appA2H H2; auto.
Qed.

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  split; intros; [appA2G; eapply MKT33; eauto|appA2H H0; auto].
Qed.

(* Theo39  μ is not a set *)

(* 一个不是集的类 *)
Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  TF (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \}).
  - New H. appA2H H; auto.
  - intro. apply H,AxiomII; auto.
Qed.

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intro. apply Lemma_N. eapply MKT33; eauto.
Qed.

Fact singlex : ∀ x, Ensemble x -> x ∈ [x].
Proof.
  intros. appA2G.
Qed.

Global Hint Resolve singlex : core.

(* Theo41  if x is a set, then for each y, y∈[x] iff y=x *)
Theorem MKT41 : ∀ x, Ensemble x -> (∀ y, y ∈ [x] <-> y = x).
Proof.
  split; intros; [appA2H H0; auto|subst; appA2G].
Qed.

Ltac eins H := apply MKT41 in H; subst; eauto.

(* Theo42  if x is a set, the [x] is a set *)
Theorem MKT42 : ∀ x, Ensemble x -> Ensemble ([x]).
Proof.
  intros. New (MKT38a H). eapply MKT33; eauto.
  red; intros. eins H1. appA2G.
Qed.

Global Hint Resolve MKT42 : core.

(* Theo43  [x]=μ iff x is not a set*)
Theorem MKT43 : ∀ x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - intro. apply MKT39. rewrite <-H; auto.
  - eqext; eauto. appA2G; intro; elim H; auto.
Qed.

(* Theo42'  if [x] is a set, then x is a set *)
Theorem MKT42' : ∀ x, Ensemble ([x]) -> Ensemble x.
Proof.
  intros. Absurd. apply MKT43 in H0.
  elim MKT39. rewrite <-H0; auto.
Qed.

(* Theo44  if x is a set, then ∩[x]=x and ∪[x]=x;
           if x is not a set, then ∩[x]=0 and ∪[x]=u *)
Theorem MKT44 : ∀ {x}, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  split; intros; eqext; try appA2G.
  - appA2H H0. apply H1; auto.
  - intros. eins H1.
  - appA2H H0. rdeHex. eins H2; subst; auto.
Qed.

Theorem MKT44' : ∀ x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros. apply MKT43 in H.
  rewrite H; split; symmetry; [apply MKT34|apply MKT34'].
Qed.

Corollary AxiomIV': ∀ x y, Ensemble (x ∪ y)
  -> Ensemble x /\ Ensemble y.
Proof.
  split; intros; eapply MKT33; eauto; red; intros; deGun; auto.
Qed.

(* Theo46  if x is a set and y is a set, 
           then [x|y] is a set and z∈[x|y] iff z=x orz=y;
           [x|y]=μ iff x or y is not a set *)
Theorem MKT46a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x|y]).
Proof.
  intros; apply AxiomIV; apply MKT42; auto.
Qed.

Global Hint Resolve MKT46a : core.

Theorem MKT46b : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∀ z, z ∈ [x|y] <-> (z = x \/ z = y)).
Proof.
  split; unfold Unordered; intros.
  - deHun; eins H1.
  - deGun. destruct H1; subst; auto.
Qed.

Theorem MKT46' : ∀ x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  split; intros.
  - Absurd. apply notandor in H0 as []. elim MKT39.
    rewrite <-H. apply MKT46a; apply NNPP; auto.
  - unfold Unordered; destruct H; apply MKT43 in H;
    rewrite H; [rewrite MKT6|]; apply MKT20.
Qed.

(* Theo47  if x and y are sets, then ∩[x|y] = x∩y and ∪[x|y] = x∪y;
           if either x or y is not a set, then ∩[x|y] = Φ and ∪[x|y] = u *)
Theorem MKT47a : ∀ x y, Ensemble x -> Ensemble y -> ∩[x|y] = x ∩ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - split; apply H2; deGun; auto.
  - destruct H2; intros. deHun; eins H4.
Qed.

Theorem MKT47b : ∀ x y, Ensemble x -> Ensemble y
  -> ∪[x|y] = x ∪ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - rdeHex. deHun; eins H3.
  - destruct H2; [exists x|exists y]; split; auto;
    apply MKT46b; auto. 
Qed.

Theorem MKT47' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros. apply MKT46' in H. rewrite H; split; symmetry;
  [apply MKT34|apply MKT34'].
Qed.

Theorem MKT49a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x,y]).
Proof.
  intros; unfold Ordered, Unordered.
  apply AxiomIV; [|apply MKT42,AxiomIV]; auto.
Qed.

Global Hint Resolve MKT49a : core.

Theorem MKT49b : ∀ x y, Ensemble ([x,y]) -> Ensemble x /\ Ensemble y.
Proof.
  intros. apply AxiomIV' in H as []. apply MKT42',
  AxiomIV' in H0 as []. split; apply MKT42'; auto.
Qed.

Theorem MKT49c1 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble x.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Theorem MKT49c2 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble y.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Ltac ope1 :=
  match goal with
    H: Ensemble ([?x,?y])
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope2 :=
  match goal with
    H: Ensemble ([?x,?y])
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope3 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope4 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope := try ope1; try ope2; try ope3; try ope4.

Theorem MKT49' : ∀ x y, ~ Ensemble ([x,y]) -> [x,y] = μ.
Proof.
  intros. apply MKT46'. apply notandor; intros [].
  apply H,AxiomIV; apply MKT42; auto.
Qed.

Fact subcp1 : ∀ x y, x ⊂ (x ∪ y).
Proof.
  unfold Included; intros. deGun; auto.
Qed.

Global Hint Resolve subcp1 : core.

(* Theo50  if x and y are sets, then ∪[x,y]=[x|y], ∩[x,y]=[x],∪∩[x,y]=x, 
                                     ∩∩[x,y]=x, ∪∪[x,y]=x∪y, ∩∪[x,y]=x∩y;
           if either x or y is not a set, then ∪∩[x,y]=Φ, ∩∩[x,y]=Φ,
                                                        ∪∪[x,y]=Φ, ∩∪[x,y]=Φ     *)
Lemma Lemma50a : ∀ x y, Ensemble x -> Ensemble y -> ∪[x,y] = [x|y].
Proof.
  intros; unfold Ordered. rewrite MKT47b; auto.
  apply MKT29; unfold Unordered; auto.
Qed.

Lemma Lemma50b : ∀ x y, Ensemble x -> Ensemble y -> ∩[x,y] = [x].
Proof.
  intros; unfold Ordered. rewrite MKT47a; auto.
  apply MKT30; unfold Unordered; auto.
Qed.

Theorem MKT50 : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\ (∪(∩[x,y]) = x)
    /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  repeat split; intros; repeat rewrite Lemma50a;
  repeat rewrite Lemma50b; auto; 
  [apply MKT44|apply MKT44|apply MKT47b|apply MKT47a]; auto.
Qed.

Lemma Lemma50' : ∀ (x y: Class), ~ Ensemble x \/ ~ Ensemble y
  -> ~ Ensemble ([x]) \/ ~ Ensemble ([x | y]).
Proof.
  intros. elim H; intros.
  - left; apply MKT43 in H0; auto. rewrite H0; apply MKT39; auto.
  - right; apply MKT46' in H; auto. rewrite H; apply MKT39; auto.
Qed.

Theorem MKT50' : ∀ {x y}, ~ Ensemble x \/ ~ Ensemble y
  -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ) /\ (∪(∪[x,y]) = μ)
    /\ (∩(∪[x,y]) = Φ).
Proof.
  intros. apply Lemma50',MKT47' in H as [].
  unfold Ordered. repeat rewrite H; repeat rewrite H0; repeat split;
  [apply MKT24'|apply MKT24|rewrite <-MKT34'|rewrite MKT34]; auto.
Qed.

(* Theo53  2nd coordinate of μ is μ *)
Theorem MKT53 : Second μ = μ.
Proof.
  intros; unfold Second, Setminus.
  repeat rewrite <-MKT34'; repeat rewrite <-MKT34.
  rewrite MKT24',MKT17,MKT21,MKT5'; auto.
Qed.

(* Theo54  if x and y are sets,
           then the 1st coordinate of [x,y] is x and the 2nd is y;
           if not, both the 1st and 2nd are μ *)
Theorem MKT54a : ∀ x y, Ensemble x -> Ensemble y
  -> First ([x,y]) = x.
Proof.
  intros; unfold First. apply MKT50; auto.
Qed.

Theorem MKT54b : ∀ x y, Ensemble x -> Ensemble y
  -> Second ([x,y]) = y.
Proof.
  intros; unfold Second. New (MKT50 H H0). deand.
  rewrite H6,H5,H3. eqext.
  - appA2H H7. deor; [appA2H H8; tauto|].
    apply setminp in H8 as []. appA2H H8; tauto.
  - appA2G. TF (z ∈ x); [left; appA2G|].
    right. apply setminP; auto. appA2G.
Qed.

Theorem MKT54' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> First ([x,y]) = μ /\ Second ([x,y]) = μ.
Proof.
  intros. New (MKT50' H). deand. unfold First, Second; split; auto.
  rewrite H3,H2,H0,MKT17. unfold Setminus.
  rewrite MKT6',MKT20'. apply MKT21.
Qed.

(* Theo55  if x and y are sets and [x,y]=[u,v], then z=x and y=v *)
Theorem MKT55 : ∀ x y u v, Ensemble x -> Ensemble y
  -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  split; intros; [|destruct H1; subst; auto].
  assert (Ensemble ([x,y])); auto. rewrite H1 in H2.
  apply MKT49b in H2 as []. rewrite <-(MKT54a x y),H1,
  <-(MKT54b x y),H1,MKT54a,MKT54b; auto.
Qed.

Fact Pins : ∀ a b c d, Ensemble c -> Ensemble d
  -> [a,b] ∈ [[c,d]] -> a = c /\ b = d.
Proof.
  intros. eins H1. symmetry in H1. apply MKT55 in H1 as []; auto.
Qed.

Ltac pins H := apply Pins in H as []; subst; eauto.

Fact Pinfus : ∀ a b f x y, Ensemble x -> Ensemble y
  -> [a,b] ∈ (f ∪ [[x,y]]) -> [a,b] ∈ f \/ (a = x /\ b = y).
Proof.
  intros. deHun; auto. pins H1. 
Qed.

Ltac pinfus H := apply Pinfus in H as [?|[]]; subst; eauto.

Ltac eincus H := apply AxiomII in H as [_ [H|H]]; try eins H; auto.

Ltac PP H a b := apply AxiomII in H as [? [a [b []]]]; subst.

Fact AxiomII' : ∀ a b P,
  [a,b] ∈ \{\ P \}\ <-> Ensemble ([a,b]) /\ (P a b).
Proof.
  split; intros.
  - PP H x y. apply MKT55 in H0 as []; subst; auto; ope.
  - destruct H. appA2G.
Qed.

Ltac appoA2G := apply AxiomII'; split; eauto.

Ltac appoA2H H := apply AxiomII' in H as [].

(* Theo58  (r∘s)∘t=r∘(s∘t) *)
Theorem MKT58 : ∀ r s t, (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; eqext.
  - PP H a b. rdeHex. appoA2H H1. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
Qed.

(* Theo59  r∘(s∪t)=r∘s∪r∘t; r∘(s∩t)⊂r∩s∘r∩t *)
Theorem MKT59 : ∀ r s t, Relation r -> Relation s
  -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t)
    /\ r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  split; try red; intros; try eqext.
  - PP H1 a b. rdeHex. deHun; deGun; [left|right]; appoA2G.
  - deHun; PP H1 a b; rdeHex; appoA2G; 
    exists x; split; auto; deGun; auto.
  - PP H1 a b. rdeHex. deHin. deGin; appoA2G.
Qed.

Fact invp1 : ∀ a b f, [b,a] ∈ f⁻¹ <-> [a,b] ∈ f.
Proof.
  split; intros; [appoA2H H; tauto|appoA2G; apply MKT49a; ope].
Qed.

Fact uiv : ∀ a b, (a ∪ b)⁻¹ = a⁻¹ ∪ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHun; apply invp1 in H0; deGun; auto.
  - deHun; PP H x y; appoA2G; deGun; auto.
Qed.

Fact iiv : ∀ a b, (a ∩ b)⁻¹ = a⁻¹ ∩ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHin; deGin; apply invp1; auto.
  - deHin; PP H x y. apply invp1; deGin; [|apply invp1]; auto.
Qed.

Fact siv : ∀ a b, Ensemble a -> Ensemble b -> [[a,b]]⁻¹ = [[b,a]].
Proof.
  intros. eqext.
  - PP H1 x y. pins H3.
  - eins H1. appoA2G.
Qed.

(* Theo61  (r ⁻¹)⁻¹=r *)
Theorem MKT61 : ∀ r, Relation r -> (r⁻¹)⁻¹ = r.
Proof.
  intros; eqext.
  - PP H0 a b. appoA2H H2; auto.
  - New H0. apply H in H0 as [? [?]]; subst.
    appoA2G. apply invp1; auto.
Qed.

(* Theo62  (r∘s)⁻¹=(s⁻¹)∘(r⁻¹) *)
Theorem MKT62 : ∀ r s, (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; eqext.
  - PP H a b. appoA2H H1. rdeHex.
    appoA2G. exists x. split; appoA2G; apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. appoA2H H1.
    apply invp1. appoA2G. apply MKT49a; ope.
Qed.

Fact opisf : ∀ a b, Ensemble a -> Ensemble b -> Function ([[a,b]]).
Proof.
  split; [red|]; intros; [eins H1|pins H1; pins H2].
Qed.

(* Theo64 if f and g are functions, f∘g is a function *)
Fact PisRel : ∀ P, Relation \{\ P \}\.
Proof.
  unfold Relation; intros. PP H a b; eauto.
Qed.

Global Hint Resolve PisRel : core.

Theorem MKT64 : ∀ f g, Function f -> Function g -> Function (f ∘ g).
Proof.
  split; intros; unfold Composition; auto.
  appoA2H H1. appoA2H H2. rdeHex. destruct H0.
  apply H with x0; auto. rewrite (H7 x x0 x1); auto.
Qed.

Corollary Property_dom : ∀ {x y f}, [x,y] ∈ f -> x ∈ dom(f).
Proof.
  intros. appA2G. ope.
Qed.

Corollary Property_ran : ∀ {x y f}, [x,y] ∈ f -> y ∈ ran(f).
Proof.
  intros. appA2G. ope.
Qed.

Fact deqri : ∀ f, dom(f) = ran(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex;
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact reqdi : ∀ f, ran(f) = dom(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex; 
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact subdom : ∀ {x y}, x ⊂ y -> dom(x) ⊂ dom(y).
Proof.
  unfold Included; intros. appA2H H0. rdeHex. appA2G.
Qed.

Fact undom : ∀ f g, dom(f ∪ g) = dom(f) ∪ dom(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; appA2H H; rdeHex;
    appA2G; exists x; deGun; auto.
Qed.

Fact unran : ∀ f g, ran(f ∪ g) = ran(f) ∪ ran(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; apply AxiomII in H as [? []];
    appA2G; exists x; deGun; auto.
Qed.

Fact domor : ∀ u v, Ensemble u -> Ensemble v -> dom([[u,v]]) = [u].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact ranor : ∀ u v, Ensemble u -> Ensemble v -> ran([[u,v]]) = [v].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact fupf : ∀ f x y, Function f -> Ensemble x -> Ensemble y
  -> ~ x ∈ dom(f) -> Function (f ∪ [[x,y]]).
Proof.
  repeat split; try red; intros.
  - destruct H. deHun; auto. eins H3.
  - pinfus H3; pinfus H4; [eapply H; eauto|..];
    elim H2; eapply Property_dom; eauto.
Qed.

Fact dos1 : ∀ {f x} y, Function f -> [x,y] ∈ f
  -> dom(f ~ [[x,y]]) = dom(f) ~ [x].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_dom in H2.
    apply setminP; auto. intro. eins H5; ope.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

Fact ros1 : ∀ {f x y}, Function f⁻¹ -> [x,y] ∈ f
  -> ran(f ~ [[x,y]]) = ran(f) ~ [y].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_ran in H2.
    apply setminP; auto. intro. eins H5; ope.
    New H0. apply invp1 in H0. apply invp1 in H4.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

(* Theo67 both domain μ and range μ are μ *)
Theorem MKT67a: dom(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

Theorem MKT67b: ran(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

Theorem MKT69a : ∀ {x f}, x ∉ dom(f) -> f[x] = μ.
Proof.
  intros. unfold Value. rewrite <-MKT24. f_equal.
  eqext; try emf. appA2H H0. elim H. eapply Property_dom; eauto.
Qed.

Theorem MKT69b : ∀ {x f}, x ∈ dom(f) -> f[x] ∈ μ.
Proof.
  intros. appA2H H. destruct H0. apply MKT19,MKT35,NEexE.
  exists x0. appA2G. ope.
Qed.

Theorem MKT69a' : ∀ {x f}, f[x] = μ -> x ∉ dom(f).
Proof.
  intros. intro. elim MKT39. New (MKT69b H0). rewrite <-H ; eauto.
Qed.

Theorem MKT69b' : ∀ {x f}, f[x] ∈ μ -> x ∈ dom(f).
Proof.
  intros. Absurd. apply MKT69a in H0. rewrite H0 in H.
  elim MKT39; eauto.
Qed.

Corollary Property_Fun : ∀ y f x, Function f
  -> [x,y] ∈ f -> y = f[x].
Proof.
  intros; destruct H. eqext.
  - appA2G; intros. appA2H H3. rewrite (H1 _ _ _ H4 H0); auto.
  - appA2H H2. apply H3. appA2G. ope.
Qed.

Lemma uvinf : ∀ z a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (z ∈ dom(f) -> (f ∪ [[a,b]])[z] = f[z]).
Proof.
  intros; eqext; appA2H H3; appA2G; intros.
  - apply H4. appA2H H5. appA2G. deGun; auto.
  - apply H4; appA2H H5. appA2G. pinfus H6. tauto.
Qed.

Lemma uvinp : ∀ a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (f ∪ [[a,b]])[a] = b.
Proof.
  intros; apply AxiomI; split; intros.
  - appA2H H2. apply H3. appA2G. deGun; auto.
  - appA2G; intros. appA2H H3. pinfus H4. elim H.
    eapply Property_dom; eauto.
Qed.

Fact Einr : ∀ {f z}, Function f -> z ∈ ran(f)
  -> ∃ x, x ∈ dom(f) /\ z = f[x].
Proof.
  intros. appA2H H0. destruct H1. New H1. apply Property_dom in H1.
  apply Property_Fun in H2; eauto.
Qed.

Ltac einr H := New H; apply Einr in H as [? []]; subst; auto.

(* Theo70 if f is a function, then f={[x,y]:y=f[x]} *)
Theorem MKT70 : ∀ f, Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; eqext.
  - New H0. apply H in H0 as [? [?]]. subst. appoA2G.
    apply Property_Fun; auto.
  - PP H0 a b. apply MKT49b in H0 as [].
    apply MKT19,MKT69b' in H1. appA2H H1. destruct H2.
    rewrite <-(Property_Fun x); auto.
Qed.

(* properties of function value *)
Corollary Property_Value : ∀ {f x}, Function f -> x ∈ dom(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. New (MKT69b H0). appoA2G.
Qed.

Fact subval : ∀ {f g}, f ⊂ g -> Function f -> Function g
  -> ∀ u, u ∈ dom(f) -> f[u] = g[u].
Proof.
  intros. apply Property_Fun,H,Property_Value; auto.
Qed.

Corollary Property_Value' : ∀ f x, Function f -> f[x] ∈ ran(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. appoA2G. apply MKT49a; eauto.
  exists dom(f). apply MKT69b', MKT19; eauto.
Qed.

Corollary Property_dm : ∀ {f x}, Function f -> x ∈ dom(f)
  -> f[x] ∈ ran(f).
Proof.
  intros. apply Property_Value in H0; auto. appA2G. ope. 
Qed.

(* Theo71 if both f and g are functions,
          then f=g iff for each x, f[x]=g[x] *)
Theorem MKT71 : ∀ f g, Function f -> Function g -> (f = g <-> ∀ x, f[x] = g[x]).
Proof.
  split; intros; subst; auto.
  rewrite (MKT70 f),(MKT70 g); auto. eqext; PP H2 a b; appoA2G.
Qed.

Ltac xo :=
  match goal with
    |- Ensemble ([?a, ?b]) => try apply MKT49a
  end.

Ltac rxo := eauto; repeat xo; eauto.

(* Theo73  if u and y are set, then [u]×y is set *)
Lemma Ex_Lemma73 : ∀ {u y}, Ensemble u -> Ensemble y
  -> let f:= \{\ λ w z, w ∈ y /\ z = [u,w] \}\ in
    Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists [u,z]. appoA2G; rxo.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appoA2G.
    + appA2G. PP H1 a b. deand. eins H2. exists b. appoA2G.
Qed.

Theorem MKT73 : ∀ u y, Ensemble u -> Ensemble y
  -> Ensemble ([u] × y).
Proof.
  intros. New (Ex_Lemma73 H H0). destruct H1,H2.
  rewrite <-H2 in H0. rewrite <-H3. apply AxiomV; auto.
Qed.

(* Theo74 if x and y are sets, then x×y is set *)
Lemma Ex_Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> let f := \{\ λ u z, u ∈ x /\ z = [u] × y \}\ in
    Function f /\ dom(f) = x
    /\ ran(f) = \{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists ([z] × y). appoA2G; rxo. apply MKT73; eauto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appA2G.
    + appA2G. appA2H H1. rdeHex. exists x0. appoA2G.
Qed.

Lemma Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> ∪(\{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}) = x × y.
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. appA2H H3. rdeHex. subst.
    PP H2 a b. deand. eins H5. subst. appoA2G.
  - PP H1 a b. deand. appA2G. exists [a] × y. split; try appoA2G.
    appA2G; rxo. apply MKT73; eauto.
Qed.

Theorem MKT74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble (x × y).
Proof.
  intros. New (Ex_Lemma74 H H0). destruct H1,H2.
  rewrite <-Lemma74,<-H3; auto. rewrite <-H2 in H.
  apply AxiomVI,AxiomV; auto.
Qed.

(* Theo75 if f is a function and domain f is a set, then f is a set *)
Theorem MKT75 : ∀ f, Function f -> Ensemble dom(f) -> Ensemble f.
Proof.
  intros. New (MKT74 H0 (AxiomV H H0)). eapply MKT33; eauto.
  red; intros. New H2. apply H in H2 as [? []]. subst.
  appoA2G; split; [eapply Property_dom|eapply Property_ran]; eauto.
Qed.

Fact fdme : ∀ {f}, Function f -> Ensemble f -> Ensemble dom(f).
Proof.
  intros. set (g := \{\ λ u v, u ∈ f /\ v = First u \}\).
  assert (Function g).
  { unfold g; split; intros; auto.
    appoA2H H1. appoA2H H2. deand; subst; auto. }
  assert (dom(g) = f).
  { eqext.
    - appA2H H2. rdeHex. appoA2H H3; tauto.
    - appA2G. exists (First z). appA2G. rxo. New H2.
      apply H in H2 as [? []]. subst. rewrite MKT54a; ope. }
  assert (ran(g) = dom(f)).
  { eqext.
    - appA2H H3. rdeHex. appoA2H H4. deand. subst z.
      New H5. apply H in H5 as [? []]. subst x.
      rewrite MKT54a; ope. eapply Property_dom; eauto.
    - appA2H H3. rdeHex. appA2G. exists [z,x]. appoA2G.
      split; auto. rewrite MKT54a; ope; auto. }
  rewrite <-H3. rewrite <-H2 in H0. apply AxiomV; auto.
Qed.

Fact frne : ∀ {f}, Function f -> Ensemble f -> Ensemble ran(f).
Proof.
  intros. apply AxiomV; [|apply fdme]; auto. 
Qed.

(* Theo77 if x and y are sets, then Exponent y x is set *)
Theorem MKT77 : ∀ x y, Ensemble x -> Ensemble y
  -> Ensemble (Exponent y x).
Proof.
  intros. apply MKT33 with (x := (pow(x × y))).
  - apply MKT38a,MKT74; auto.
  - red; intros. apply MKT38b; [apply MKT74; auto|].
    red; intros. appA2H H1. deand. New H2. apply H3 in H2 as [? []].
    subst. New (Property_dom H6). New (Property_ran H6). appoA2G.
Qed.

Fact Property_Asy : ∀ {r x u}, Asymmetric r x -> u ∈ x
  -> ~ Rrelation u r u.
Proof.
  intros; intro; eapply H; eauto.
Qed.

Corollary wosub : ∀ x r y, WellOrdered r x -> y ⊂ x
  -> WellOrdered r y.
Proof.
  unfold WellOrdered, Connect; intros; destruct H; split; intros.
  - apply H; auto.
  - apply (H1 _ (MKT28 H2 H0) H3).
Qed.

(* Theo88 *)
Theorem MKT88a : ∀ {r x}, WellOrdered r x -> Asymmetric r x.
Proof.
  intros * []. red; intros; intro.
  assert ([u | v] ⊂ x).
  { red; intros. apply MKT46b in H5 as []; subst; eauto. }
  assert ([u | v] ≠ Φ).
  { apply NEexE; exists u. apply MKT46b; eauto. }
  destruct (H0 _ H5 H6) as [z []].
  apply MKT46b in H7 as []; subst; eauto;
  [apply (H8 v)|apply (H8 u)]; auto; apply MKT46b; eauto. 
Qed.

Theorem MKT88b : ∀ r x, WellOrdered r x -> Transitive r x.
Proof.
  intros. New (MKT88a H). destruct H. red; intros.
  destruct (H _ _ H2 H4) as [?|[?|?]]; auto.
  - assert ([u] ∪ [v] ∪ [w] ⊂ x). { red; intros. deHun; eins H8. }
    assert ([u] ∪ [v] ∪ [w] ≠ Φ).
    { apply NEexE; exists u. deGun. eauto. }
    destruct (H1 _ H8 H9) as [z []]. deHun; eins H10; 
    [destruct (H11 w)|destruct (H11 u)|destruct (H11 v)]; auto.
    + deGun. right. deGun. eauto.
    + deGun. eauto.
    + deGun. right. deGun. eauto.
  - subst; destruct (H0 _ _ H2 H3); auto.
Qed.

(* Theo90 *)
Theorem MKT90 : ∀ n x r, n ≠ Φ -> (∀ y, y ∈ n -> rSection y r x)
  -> rSection (∩n) r x /\ rSection (∪n) r x.
Proof.
  intros. NEele H. New H. apply H0 in H as [? []].
  split; split; try split; auto; try red; intros.
  - appA2H H4; auto.
  - appA2G; intros. New H7. appA2H H5. apply H9 in H8.
    destruct (H0 _ H7) as [? []]. eapply H12; eauto.
  - appA2H H4. rdeHex. apply (H0 _ H6); auto.
  - appA2H H5. rdeHex. destruct (H0 _ H8) as [? []]. appA2G.
Qed.

(* Theo91 *)
Theorem MKT91 : ∀ {x y r}, rSection y r x ->  y <> x
  -> (∃ v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros. assert (∃ v, FirstMember v r (x ~ y)).
  { apply H.
    - red; intros. apply MKT4' in H1; tauto.
    - intro. apply H0. destruct H. apply MKT27; split; auto.
      red; intros. Absurd. feine z. rewrite <-H1; auto. }
  destruct H1 as [v []]. apply setminp in H1 as [].
  exists v; split; auto. destruct H as [? []]. eqext.
  - appA2G. split; auto. destruct H4.
    New (H4 _ _ H1 (H _ H6)). deor; auto.
    + elim H3. eapply H5; eauto.
    + subst. elim H3; auto.
  - appA2H H6. deand. Absurd. destruct (H2 z); auto.
Qed.

(* Theo92 *)
Theorem MKT92 : ∀ {x y z r}, rSection x r z -> rSection y r z
  -> x ⊂ y \/ y ⊂ x.
Proof.
  intros. TF (x ⊂ y); auto.
  right; red; intros. destruct H,H0,H3,H4.
  assert (∃ z1,z1 ∈ x /\ ~ (z1 ∈ y)).
  { Absurd. elim H1. red; intros. Absurd. elim H7; eauto. }
  rdeHex. apply H5 with x0; auto. destruct H3.
  New (H3 _ _ (H0 _ H2) (H _ H7)). deor; auto.
  - elim H8. eapply H6; eauto.
  - subst. elim H8; auto.
Qed.

(* Theo94 *)
Theorem MKT94 : ∀ {x r y f}, rSection x r y -> Order_Pr f r r
  -> On f x -> To f y -> (∀ u, u ∈ x -> ~ Rrelation f[u] r u).
Proof.
  intros; intro. destruct H,H5,H5,H0,H8,H9,H1,H2 as [_].
  assert (u ∈ \{ λ u, u ∈ x /\ Rrelation f[u] r u \} ). { appA2G. }
  assert (∃ z, FirstMember z r \{ λ u, u ∈ x
    /\ Rrelation f[u] r u \}).
  { apply H7; [|apply NEexE; eauto].
    red; intros. appA2H H13. deand. auto. }
  destruct H13 as [v []]. appA2H H13. deand. subst x.
  assert (f[v] ∈ y). { apply H2, Property_dm; auto. }
  New (H6 _ _ H11 H15 H16). New (H10 _ _ H17 H15 H16).
  apply H14 with f[v]; auto. appA2G.
Qed.

Lemma f11vi : ∀ f u, Function f -> Function f⁻¹ -> u ∈ ran(f)
  -> f[(f⁻¹)[u]] = u.
Proof.
  intros. rewrite reqdi in H1. apply Property_Value in H1; auto.
  apply ->invp1 in H1; auto. apply Property_Fun in H1; auto.
Qed.

Lemma f11inj : ∀ f a b, Function f -> Function f⁻¹
  -> a ∈ dom(f) -> b ∈ dom(f) -> f[a] = f[b] -> a = b.
Proof.
  intros. destruct H0. eapply H4 with f[a]; apply invp1;
  [|rewrite H3]; apply Property_Value; auto.
Qed.

Lemma f11iv : ∀ f u, Function f -> Function f⁻¹ -> u ∈ dom(f)
  -> (f⁻¹)[f[u]] = u.
Proof.
  intros. apply Property_Value,invp1,Property_Fun in H1; auto.
Qed.

Fact f11pa : ∀ {f x y}, Function1_1 f -> [x,y] ∈ f
  -> Function1_1 (f ~ [[x,y]]).
Proof.
  intros * [] ?. repeat split; try red; intros.
  - appA2H H2. apply H; tauto.
  - apply setminp in H2. apply setminp in H3. deand.
    eapply H; eauto.
  - PP H2 a b; eauto.
  - appoA2H H2. appoA2H H3. apply setminp in H4.
    apply setminp in H5. deand. eapply H0; apply invp1; eauto.
Qed.

Fact f11pb : ∀ f x y, Function1_1 f -> Ensemble x -> Ensemble y
  -> ~ x ∈ dom(f) -> ~ y ∈ ran(f) -> Function1_1 (f ∪ [[x,y]]).
Proof.
  intros. destruct H. split.
  - apply fupf; auto.
  - rewrite reqdi in H3. rewrite uiv.
    rewrite siv; auto. apply fupf; auto.
Qed.

(* Theo96 *)
Theorem MKT96a : ∀ {f r s}, Order_Pr f r s -> Function1_1 f.
Proof.
  intros. destruct H as [? [? []]].
  split; auto; split; try red; intros.
  - PP H3 a b. eauto.
  - apply ->invp1 in H3. apply ->invp1 in H4. New H3. New H4.
    apply Property_Fun in H3; apply Property_Fun in H4; subst; auto.
    New (Property_dom H5). New (Property_dom H6).
    New (Property_ran H6). destruct H0.
    New (H0 _ _ H3 H7). deor; auto.
    + New (H2 _ _ H3 H7 H10). rewrite <-H4 in H11.
      destruct (MKT88a H1 _ _ H8 H8 H11); auto.
    + New (H2 _ _ H7 H3 H10). rewrite <-H4 in H11.
      destruct (MKT88a H1 _ _ H8 H8 H11); auto.
Qed.

Theorem MKT96b : ∀ {f r s}, Order_Pr f r s -> Order_Pr (f⁻¹) s r.
Proof.
  intros. destruct (MKT96a H) as [_]. red in H. deand.
  red. rewrite <-deqri,<-reqdi. deandG; auto. intros.
  New H4. New H5. destruct H1. einr H7. einr H8.
  rewrite f11iv,f11iv; auto. apply MKT88a in H2.
  New (H1 _ _ H7 H8). deor; subst; auto.
  - New (H3 _ _ H8 H7 H12). destruct (H2 f[x] f[x0]); auto.
  - destruct (H2 f[x0] f[x0]); auto.
Qed.

Theorem MKT96 : ∀ f r s, Order_Pr f r s
  -> Function1_1 f /\ Order_Pr (f⁻¹) s r.
Proof.
  split; intros; [eapply MKT96a|apply MKT96b]; eauto.
Qed.

(* Theo97 *)
Lemma lem97a :  ∀ f g u r s x y, Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y
  -> FirstMember u r (\{ λ a, a ∈ (dom(f) ∩ dom(g))
    /\ f [a] <> g [a] \}) -> Rrelation f[u] s g[u] -> False.
Proof.
  intros. New H0. apply MKT96b in H as G.
  destruct H as [H _],H0 as [H0],H8,H9,H3,H11,H4,H5,H13.
  appA2H H5. deand. deHin. New H16; New H18.
  apply Property_dm in H16; apply Property_dm in H18; auto.
  New (H15 _ _ (H3 _ H16) H18 H6). apply AxiomII in H21 as [_ [v]].
  New (Property_dom H21). apply Property_Fun in H21; auto.
  rewrite H21 in H6. assert (Rrelation v r u).
  { apply MKT96b in H7 as [? [_ [_ ?]]]. New H22.
    apply Property_dm in H22; auto. rewrite reqdi in H22,H18.
    New (H23 _ _ H22 H18 H6). do 2 rewrite f11iv in H25; auto. }
  destruct H1 as [? []],H2 as [? []].
  New (H25 _ _ (H2 _ H22) H19 H23). apply (H14 v); auto.
  appA2G. split; deGin; auto. intro. rewrite <-H21 in H29.
  destruct G as [? _]. eapply f11inj in H29; eauto. subst.
  eapply Property_Asy; eauto. apply MKT88a; auto.
Qed.

Lemma le97 : ∀ f g, Function f -> Function g
  -> (∀ a, a ∈ (dom(f) ∩ dom(g)) -> f[a] = g[a])
  -> dom(f) ⊂ dom(g) -> f ⊂ g.
Proof.
  intros. apply MKT30 in H2. rewrite H2 in H1. red; intros.
  New H3. rewrite MKT70 in H3; auto. PP H3 a b.
  apply Property_dom in H4. rewrite H1 in *; auto.
  rewrite MKT70; auto. appoA2G.
Qed.

Theorem MKT97 :  ∀ {f g r s x y}, Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros. TF (∀ a, a ∈ (dom(f) ∩ dom(g)) -> f[a] = g[a]).
  - destruct H,H0, (MKT92 H1 H2); apply le97 in H8; auto.
    intros. rewrite H5; auto. rewrite MKT6'; auto.
  - assert (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] <> g[a] \} <> Φ).
    { intro. apply H5; intros. Absurd.
      feine a. rewrite <-H6. appA2G. }
    assert (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] <> g[a] \}
       ⊂ dom(f)).
    { red; intros. appA2H H7. deand. deHin; auto. }
    inversion H1 as [? [[_ ?] _]].
    destruct (H9 _ (MKT28 H7 H8) H6) as [u].
    inversion H10. apply AxiomII in H11 as [_ []]. deHin.
    inversion H as [? _]. inversion H0 as [? _].
    apply Property_dm in H11; apply Property_dm in H14; auto.
    inversion H3 as [? [[? _] _]]. inversion H4 as [? _].
    destruct (H18 f[u] g[u]) as [?|[?|?]]; auto; try tauto;
    eapply lem97a in H20; eauto; try tauto. destruct H10.
    appA2H H10. deand. rewrite MKT6'. split; intros.
    + appA2G.
    + apply AxiomII in H24 as [? []]. apply H12; appA2G.
Qed.

(* Theo99 *)
Lemma Lemma99c : ∀ y r x a b, rSection y r x -> a ∈ y -> ~ b ∈ y
  -> b ∈ x -> Rrelation a r b.
Proof.
  intros * [? [[]]]; intros. New (H0 _ _ (H _ H3) H5). deor; auto.
  - elim H4. eapply H2; eauto.
  - subst; tauto.
Qed.

Ltac RN a b := rename a into b.

Theorem MKT99 : ∀ {r s x y}, WellOrdered r x -> WellOrdered s y
  -> ∃ f, Function f /\ Order_PXY f x y r s
    /\(dom(f) = x \/ ran(f) = y).
Proof.
  intros. set (f := \{\ λ u v, u ∈ x /\ (∃ g, Function g
    /\ Order_PXY g x y r s /\ u ∈ dom(g) /\ [u,v] ∈ g ) \}\).
  assert (Function f).
  { split; intros; unfold f; auto. appoA2H H1. appoA2H H2.
    deand. rdeHex. RN x2 g1. RN x1 g2. red in H7, H10. deand.
    destruct (MKT97 H18 H14 H19 H15 H20 H16);
    [eapply H5|eapply H6]; eauto. }
  assert (rSection dom(f) r x).
  { split; [|split]; try red; intros; auto.
    - appA2H H2. rdeHex. appoA2H H3. tauto.
    - appA2H H3. rdeHex. appoA2H H5. deand. rdeHex. RN x1 g.
      inversion H8. deand. destruct H14,H16.
      New (H17 _ _ H2 H9 H4). appA2G. exists g[u]. New H18. New H18.
      apply Property_dm in H18; apply Property_Value in H19; auto.
      appoA2G; repeat split; rxo. }
  assert (rSection ran(f) s y).
  { split; [|split]; try red; intros; auto.
    - appA2H H3. rdeHex. appoA2H H4. deand. rdeHex. RN x1 g.
      deand. apply Property_ran,H7 in H9. auto.
    - appA2H H4. rdeHex. appoA2H H6. deand. rdeHex. RN x1 g.
      inversion H9. deand. destruct H16 as [? []].
      apply Property_ran in H11. New (H18 _ _ H3 H11 H5).
      apply AxiomII in H19 as [? [z]]. New H20.
      apply Property_dom in H20. New H20.
      apply Property_Value in H20; auto.
      apply Property_Fun in H21; auto. subst. destruct H15.
      appA2G. exists z. appoA2G. split; eauto. }
  assert (Order_PXY f x y r s).
  { red; deandG; auto. destruct H2 as [? []],H3 as [? []].
    red; deandG; try eapply wosub; eauto; intros.
    apply Property_Value in H8; apply Property_Value in H9; auto.
    appoA2H H8. appoA2H H9. deand. rdeHex.
    destruct H15 as [_ [_ [? []]]],H18 as [_ [_ [? []]]].
    apply Property_Fun in H17; apply Property_Fun in H20; auto.
    rewrite H20,H17. destruct (MKT97 H15 H18 H21 H23 H22 H24).
    - New (subdom H25). rewrite (subval H25); auto. apply H18; auto.
    - New (subdom H25). rewrite (subval H25); auto.
      apply H15; auto. }
  exists f. deandG; auto. Absurd. apply notandor in H5 as [].
  assert (∃ u, FirstMember u r (x ~ dom(f))).
  { apply H2; red; intros.
    - apply AxiomII in H7; tauto.
    - apply H5. destruct H2. eqext; auto. Absurd.
      feine z. rewrite <-H7. auto. }
  assert (∃ u, FirstMember u s (y ~ ran(f))).
  { apply H3; red; intros.
    - apply AxiomII in H8; tauto.
    - apply H6. destruct H3. eqext; auto. Absurd.
      feine z. rewrite <-H8. auto. }
  destruct H7 as [u []], H8 as [v []].
  apply AxiomII in H7 as [? []]. apply AxiomII in H8 as [? []].
  apply AxiomII in H12 as [_ ]. apply AxiomII in H14 as [_ ].
  elim H12. appA2G. exists v.
  appoA2G. split; auto. exists (f ∪ [[u,v]]).
  assert (Function (f ∪ [[u,v]])). { apply fupf; auto. }
  assert (rSection dom(f ∪ [[u,v]]) r x).
  { rewrite undom. destruct H2 as [? []].
    red. deandG; intros; auto. red. intros; auto.
    - deHun; auto. rewrite domor in H18; auto. eins H18.
    - deGun; deHun.
      + apply H17 in H20; auto.
      + rewrite domor in H19; auto. eins H19.
        TF (u0 ∈ dom(f)); auto. elim (H9 u0); auto. }
  assert (rSection ran(f ∪ [[u,v]]) s y).
  { rewrite unran. destruct H3 as [? []].
    red. deandG; intros; auto. red; intros; auto.
    - deHun; auto. rewrite ranor in H19; auto. eins H19.
    - deGun; deHun.
      + left. apply H18 in H21; auto.
      + rewrite ranor in H20; auto. eins H20.
        TF (u0 ∈ ran(f)); auto. elim (H10 u0); auto. }
  inversion H16 as [? []]. inversion H17 as [? []].
  deandG; intros; auto. try red; deandG; auto; try red; deandG; auto.
  - eapply wosub; eauto.
  - eapply wosub; eauto.
  - intros. rewrite undom, domor in H24, H25; auto. deHun.
    + rewrite uvinf, uvinf; auto. apply H4; auto.
    + eins H24. destruct H2 as [? []]. elim H12. eapply H27; eauto.
    + eins H25. rewrite (uvinp u), (uvinf u0); auto.
      eapply (Lemma99c ran(f)); eauto. apply Property_dm; auto.
    + eins H24. eins H25. rewrite uvinp; auto. elim (H9 u); auto.
  - rewrite undom,domor; auto. deGun. right. auto.
  - deGun. auto.
Qed.

(* Theo100 *)
Theorem MKT100 : ∀ {r s x y}, WellOrdered r x -> WellOrdered s y
  -> Ensemble x -> ~ Ensemble y -> ∃ f, Function f
    /\ Order_PXY f x y r s /\ dom( f) = x.
Proof.
  intros. destruct (MKT99 H H0) as [f]. deand.
  exists f; deandG; destruct H5; auto. subst.
  destruct H4 as [_ [_ [_ [H4 _]]]]. destruct H4. elim H2.
  apply AxiomV; auto. eapply MKT33; eauto.
Qed.

Theorem MKT100' : ∀ r s x y, WellOrdered r x /\ WellOrdered s y
  -> Ensemble x -> ~ Ensemble y
  -> ∀ f, Function f /\ Order_PXY f x y r s /\ dom(f) = x
  -> ∀ g, Function g /\ Order_PXY g x y r s /\ dom(g) = x
  -> f = g.
Proof.
  intros. deand; subst. apply MKT71; auto; intros.
  TF (x ∈ dom( f)).
  - destruct H4 as [_ [_ [? []]]],H6 as [_ [_ [? []]]].
    destruct (MKT97 H4 H6 H9 H11 H10 H12);
    [symmetry; rewrite <-H5 in H7|]; apply subval; auto.
  - rewrite (@ MKT69a x); auto. rewrite <-H5 in H7.
    rewrite MKT69a; auto.
Qed.

(* Theo 101 *)
Theorem MKT101 : ∀ x, x ∉ x.
Proof.
  intros; intro. assert ([x] ≠ Φ). { apply NEexE; exists x; eauto. }
  apply AxiomVII in H0 as [? []]. eins H0. feine x. rewrite <-H1.
  appA2G.
Qed.

(* Theo102 *)
Theorem MKT102 : ∀ x y, x ∈ y -> y ∈ x -> False.
Proof.
  intros. assert (x ∈ [x|y]) by appA2G.
  assert (y ∈ [x|y]) by appA2G.
  assert ([x|y] ≠ Φ). { apply NEexE; eauto. } 
  apply AxiomVII in H3 as [? []].
  apply MKT46b in H3 as []; subst; eauto;
  [feine y|feine x]; rewrite <-H4; appA2G.
Qed.

(* Theo104 *)
Lemma cirin3f : ∀ x y z, x ∈ y -> y ∈ z -> z ∈ x -> False.
Proof.
  intros. assert (x ∈ ([x|y] ∪ [z])). { appA2G. left. appA2G. } 
  assert (y ∈ ([x|y] ∪ [z])). { appA2G. left. appA2G. } 
  assert (z ∈ ([x|y] ∪ [z])). { appA2G. } 
  assert ([x|y] ∪ [z] ≠ Φ). { apply NEexE; eauto. }
  apply AxiomVII in H5 as [? []]. apply MKT4 in H5 as [].
  - apply MKT46b in H5 as []; subst; eauto;
    [feine z|feine x]; rewrite <-H6; appA2G.
  - eins H5. feine y; rewrite <-H6; appA2G.
Qed.

Theorem MKT104 : ~ Ensemble E.
Proof.
  intro. assert (E ∈ [E]) by appA2G.
  assert ([E] ∈ [E,[E]]) by appA2G.
  assert ([E,[E]] ∈ E) by appoA2G. eapply cirin3f; eauto.
Qed.

(* Theo107 *)
Theorem MKT107 : ∀ {x}, Ordinal x -> WellOrdered E x.
Proof.
  intros ? []; split; auto; intros. apply AxiomVII in H2 as [? []].
  exists x0; red; split; intros; auto. intro. appoA2H H5.
  feine y0. rewrite <-H3. appA2G.
Qed.

(* Theo108 *)
Theorem MKT108 : ∀ x y, Ordinal x -> y ⊂ x -> y <> x -> Full y
  -> y ∈ x.
Proof.
  intros. New (MKT107 H).
  assert (rSection y E x).
  { red; intros. deandG; auto. intros.
    appoA2H H6. eapply H2; eauto. }
  New (MKT91 H4 H1). destruct H5 as [? []].
  assert (x0 = \{ λ u,u ∈ x /\ Rrelation u E x0 \}).
  { eqext.
    - appA2G; split; [eapply H; eauto| appoA2G; rxo].
    - appA2H H7. deand. appoA2H H9. auto. }
  rewrite H6,<-H7; auto.
Qed.

(* Theo109 *)
Lemma Lemma109 : ∀ {x y}, Ordinal x -> Ordinal y
  -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros. TF ((x ∩ y) = x); auto. right. apply MKT108; auto.
  - apply MKT30. rewrite MKT6',<-MKT7',MKT5'; auto.
  - destruct H,H0. unfold Full,Included in *; intros. deHin.
    deGin; eauto.
Qed.

Theorem MKT109 : ∀ {x y}, Ordinal x -> Ordinal y
  -> x ⊂ y \/ y ⊂ x.
Proof.
  intros. destruct (Lemma109 H H0),(Lemma109 H0 H);
  try apply MKT30 in H1; try apply MKT30 in H2; auto.
  rewrite MKT6' in H2. elim (MKT101 (x ∩ y)); deGin; auto.
Qed.

(* Theo110 *)
Theorem MKT110 : ∀ {x y}, Ordinal x -> Ordinal y
  -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros. TF (x = y); auto. inversion H. inversion H0.
  destruct (MKT109 H H0); eapply MKT108 in H6; eauto.
Qed.

Corollary Th110ano : ∀ {x y}, Ordinal x -> Ordinal y
  -> x ∈ y \/ y ⊂ x.
Proof.
  intros. New (MKT110 H H0). deor; subst; auto.
  right. red; intros. eapply H; eauto.
Qed.

(* Theo111 *)
Theorem MKT111 : ∀ x y, Ordinal x -> y ∈ x -> Ordinal y.
Proof.
  intros. inversion H.
  split; unfold Connect, Full, Included in *; intros; eauto.
  apply MKT107,MKT88b in H. red in H.
  assert (Rrelation z E y).
  { New (H2 _ H0 _ H3). New (H2 _ H5 _ H4).
    apply (H z m y); auto; appoA2G; rxo. } appoA2H H5; auto.
Qed.

(* Theo113 *)
Lemma Lemma113 :∀ u v, Ensemble u -> Ensemble v -> Ordinal u
  -> Ordinal v -> (Rrelation u E v \/ Rrelation v E u \/ u = v).
Proof.
  intros. New (MKT110 H1 H2).
  deor; auto; [left|right;left]; appoA2G.
Qed.

Theorem MKT113a : Ordinal R.
Proof.
  split; red; unfold Included; intros.
  - appA2H H; appA2H H0. apply Lemma113; auto.
  - appA2H H. appA2G. eapply MKT111; eauto.
Qed.

Theorem MKT113b : ~ Ensemble R.
Proof.
  intro. elim (MKT101 R). appA2G. apply MKT113a.
Qed.

Global Hint Resolve MKT113a MKT113b : core.

(* Theo114 *)
Theorem MKT114 : ∀ x, rSection x E R -> Ordinal x.
Proof.
  intros. TF (x = R); subst; auto. destruct (MKT91 H H0) as [? []].
  assert (x0 = \{ λ u, u ∈ R /\ Rrelation u E x0 \}).
  { eqext.
    - appA2G; split; try appoA2G; rxo.
      appA2H H1. appA2G; eauto. eapply MKT111; eauto.
    - appA2H H3. deand. appoA2H H5. auto. }
  rewrite H3,<-H2 in H1. appA2H H1; auto.
Qed.

Corollary Property114 : ∀ x, Ordinal x -> rSection x E R.
Proof.
  intros. red; deandG; [|apply MKT107; auto|]; try red; intros.
  - appA2G. eapply MKT111; eauto.
  - appoA2H H2. appA2H H0. eapply H; eauto.
Qed.

(* Theo118 *)
Theorem MKT118 : ∀ x y, Ordinal x -> Ordinal y
  -> (x ⊂ y <-> x ≼ y).
Proof.
  split; red; intros.
  - New (MKT110 H H0). deor; auto.
    New (H1 _ H2). destruct (MKT101 _ H3).
  - destruct H1; subst; auto. eapply H0; eauto.
Qed.

(* Theo119 *)
Theorem MKT119 : ∀ x, Ordinal x
  -> x = \{ λ y, (y ∈ R /\ Less y x) \}.
Proof.
  intros; eqext.
  - appA2G; split; auto. appA2G. eapply MKT111; eauto.
  - appA2H H0. tauto.
Qed.

(* Theo120 *)
Theorem MKT120 : ∀ x, x ⊂ R -> Ordinal (∪x).
Proof.
  intros; split; red; unfold Included; intros.
  - appA2H H0. appA2H H1. rdeHex. New (H _ H4). New (H _ H5).
    appA2H H6. appA2H H7. eapply MKT111 in H2;
    eapply MKT111 in H3; eauto. apply Lemma113; auto.
  - appA2H H0. rdeHex. appA2G. exists x0. split; auto.
    New (H _ H3). appA2H H4. eapply H5; eauto.
Qed.

(* Theo121 *)
Lemma Lemma121 : ∀ x, x ⊂ R -> x <> Φ -> FirstMember (∩x) E x.
Proof.
  intros. New H. New (MKT107 MKT113a).
  apply H2 in H as [? []]; auto.
  assert (∩x = x0).
  { eqext; [appA2H H4; auto|].
    appA2G; intros. New (H1 _ H). New (H1 _ H5).
    appA2H H6. appA2H H7. New (MKT110 H8 H9). deor; subst; auto.
    - eapply H9; eauto.
    - elim (H3 y); auto. appoA2G. } subst; split; auto.
Qed.

Theorem MKT121 : ∀ x, x ⊂ R -> x <> Φ -> (∩x) ∈ x.
Proof.
  intros. apply Lemma121; auto. 
Qed.

(* Theo123 *)
Lemma Lem123 : ∀ x, x ∈ R -> (PlusOne x) ∈ R.
Proof.
  intros; appA2H H; appA2G; [apply AxiomIV; auto|].
  split; red; unfold Included; intros.
  - eincus H1; eincus H2.
    + destruct H0; auto.
    + left. appoA2G.
    + right. left. appoA2G.
  - eincus H1.
    + appA2G. left. eapply H0; eauto.
    + appA2G.
Qed.

Global Hint Resolve Lem123 : core.

Theorem MKT123 : ∀ x, x ∈ R
  -> FirstMember (PlusOne x) E (\{ λ y, (y ∈ R /\ Less x y) \}).
Proof.
  intros; split; intros.
  - appA2G; split; auto. appA2G.
  - intro. appoA2H H1. appA2H H0. destruct H3. eincus H2.
    + eapply MKT102; eauto.
    + eapply MKT101; eauto.
Qed.

(* Theo124 *)
Theorem MKT124 : ∀ x, x ∈ R -> ∪(PlusOne x) = x.
Proof.
  intros; eqext.
  - appA2H H0. rdeHex. eincus H2.
    appA2H H. eapply H3; eauto.
  - appA2G. exists x. split; auto. appA2G.
Qed.

(* Theo126 *)
Theorem MKT126a : ∀ f x, Function f -> Function (f|(x)).
Proof.
  split; try red; intros; destruct H.
  - appA2H H0. destruct H2; auto.
  - appA2H H0. appA2H H1. destruct H3,H4. eapply H2; eauto.
Qed.

Theorem MKT126b : ∀ f x, Function f -> dom(f|(x)) = x ∩ dom(f).
Proof.
  intros; eqext; appA2H H0; destruct H1.
  - appA2H H1. destruct H2. appoA2H H3. destruct H4.
    apply Property_dom in H2. appA2G.
  - appA2H H2. destruct H3. appA2G; exists x0; appA2G.
    split; auto. appoA2G; split; auto. apply MKT19; ope.
Qed.

Theorem MKT126c : ∀ f x, Function f
  -> (∀ y, y ∈ dom(f|(x)) -> (f|(x))[y] = f[y]).
Proof.
  intros. apply subval; auto; [|apply MKT126a]; auto.
  red; intros. appA2H H1. tauto.
Qed.

Corollary frebig : ∀ f x, Function f -> dom(f) ⊂ x -> f|(x) = f.
Proof.
  intros; eqext.
  - appA2H H1; tauto.
  - appA2G; split; auto. New H1. apply H in H1 as [? [?]].
    subst. New H2. apply Property_dom in H2. appoA2G; split; auto.
    apply MKT19; ope.
Qed.

Corollary fresub : ∀ f h, Function f -> Function h -> h ⊂ f
  -> f|(dom(h)) = h.
Proof.
  intros; eqext.
  - appA2H H2. destruct H3. PP H4 a b. destruct H6. New H5.
    eapply subval in H5; eauto. apply Property_Fun in H3; auto.
    subst. rewrite <-H5. apply Property_Value; auto.
  - appA2G; split; auto. New H2. apply H0 in H2 as [? []]. subst.
    appoA2G. split; [eapply Property_dom; eauto|apply MKT19; ope].
Qed.

Corollary fuprv : ∀ f x y z, Ensemble x -> Ensemble y
  -> ~ x ∈ z ->  (f ∪ [[x,y]])|(z) = f|(z).
Proof.
  intros. unfold Restriction. rewrite MKT6,MKT6'.
  rewrite (MKT6' f),MKT8. apply MKT29. red; intros.
  deHin. eins H3. appoA2H H2. destruct H3. elim H1; auto.
Qed.

(* Theo127 *)
Theorem MKT127 : ∀ {f h g}, Function f -> Ordinal dom(f)
  -> (∀ u, u ∈ dom(f) -> f[u] = g[f|(u)]) -> Function h
  -> Ordinal dom(h) -> (∀ u, u ∈ dom(h) -> h[u] = g[h|(u)])
  -> h ⊂ f \/ f ⊂ h.
Proof.
  intros. TF (∀ a, a ∈ (dom(f) ∩ dom(h)) -> f[a] = h[a]).
  - destruct (MKT109 H3 H0); apply le97 in H6; auto.
    rewrite MKT6'; auto; intros. symmetry; auto.
  - assert (∃ u, FirstMember u E \{λ a, a ∈ dom(f) ∩ dom(h)
      /\ f[a] <> h[a]\}).
    { apply (MKT107 MKT113a); red; intros.
      - appA2H H6. destruct H7. deHin. appA2G. eapply MKT111; eauto.
      - apply H5; intros. Absurd. feine a. rewrite <-H6; appA2G. }
    destruct H6 as [u []]. appA2H H6. destruct H8. deHin. elim H9.
    assert (f|(u) = h|(u)).
    { eqext; appA2H H11; destruct H12.
      - appA2G; split; auto; rewrite MKT70 in H12; auto.
        PP H12 a b. rewrite MKT70; auto. appoA2G. Absurd.
        appoA2H H13. destruct H15. elim (H7 a); try appoA2G.
        appA2G; split; auto. deGin; [eapply H0|eapply H3]; eauto.
      - appA2G; split; auto; rewrite MKT70 in H12; auto.
        PP H12 a b. rewrite MKT70; auto. appoA2G. Absurd.
        appoA2H H13. destruct H15. elim (H7 a); try appoA2G.
        appA2G; split; auto. deGin; [eapply H0|eapply H3]; eauto. }
    rewrite H1,H4,H11; auto.
Qed.

(* Theo128 *)
Theorem MKT128a :  ∀ g, ∃ f, Function f /\ Ordinal dom(f)
  /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)]).
Proof.
  intros. set (f := \{\ λ u v, u ∈ R
    /\ (∃ h, Function h /\ Ordinal dom(h)
    /\ (∀ z, z ∈ dom(h) -> h[z] = g[h|(z)])
    /\ [u,v] ∈ h ) \}\).
  assert (Function f).
  { split; [unfold f; auto|]; intros. appoA2H H. appoA2H H0.
    destruct H1 as [? [h1]], H2 as [? [h2]]. deand.
    destruct (MKT127 H3 H8 H9 H4 H5 H6); [eapply H3|eapply H4];
    eauto. }
  assert (Ordinal dom(f)).
  { apply MKT114; unfold rSection; deandG; intros.
    - red; intros. appA2H H0. destruct H1. appoA2H H1; tauto.
    - apply MKT107,MKT113a.
    - appA2H H1. destruct H3. appoA2H H3. destruct H4 as [? [h]].
      deand. apply Property_dom in H8. appoA2H H2.
      eapply H6 in H9; eauto. apply Property_Value in H9; auto.
      appA2G. exists h[u]. appoA2G. split; eauto. }
  assert (K1: ∀ x, x ∈ dom(f) -> f[x] = g[f|(x)]); intros.
  { appA2H H1. destruct H2. appoA2H H2.
    destruct H3 as [? [h]]. deand.
    assert (h ⊂ f); try red; intros.
    { New H8. rewrite MKT70 in H8; auto. PP H8 a b. New H9.
      apply Property_dom in H9. apply MKT111 in H9; auto.
      appoA2G; split; [appA2G;ope|eauto]. }
    apply Property_dom in H7. rewrite <-(subval H8),H6; auto.
    f_equal. eqext; appA2H H9; destruct H10; appA2G; split; auto.
    New H10. apply H in H10 as [? []]. subst. appoA2H H11.
    destruct H11. eapply H5 in H11; eauto.
    rewrite MKT70 in H12; auto. appoA2H H12. subst.
    erewrite <-subval; eauto. apply Property_Value; auto. }
  exists f. deandG; auto. intros. TF (x ∈ dom(f)); auto.
  assert (K2: ∀ z, ~ z ∈ dom(f) -> Ordinal z -> f|(z) = f); intros.
  { destruct (Th110ano H4 H0); try tauto. apply frebig; auto. }
  rewrite K2,MKT69a; auto; [|appA2H H1; auto]. TF(f ∈ dom(g)).
  - assert (∃ y, FirstMember y E (R ~ dom(f))).
    { apply (MKT107 MKT113a); red; intros.
      - appA2H H4; tauto.
      - feine x. rewrite <-H4. auto. }
    destruct H4 as [y []]. apply MKT4' in H4 as []. appA2H H6.
    apply MKT69b in H3; auto. set (h := f ∪ [[y,g[f]]]).
    assert (h ⊂ f); try red; intros.
    { appA2H H8. deor; auto. eins H9. appoA2G. split; auto.
      assert (Function h). { apply fupf; auto. }
      assert (Ordinal dom(h)).
      { apply MKT114; unfold rSection,h; deandG; intros.
        - red; intros. rewrite undom in H10. deHun.
          + appA2G. eapply MKT111; eauto.
          + rewrite domor in H10; auto. eins H10.
        - apply MKT107,MKT113a.
        - rewrite undom in H11|-*. deGun. deHun.
          + left. appoA2H H12. eapply H0; eauto.
          + rewrite domor in H11; auto. eins H11.
            appoA2H H12. left. Absurd.
            destruct (H5 u); auto. appoA2G. }
      exists h. deandG; auto; try appA2G; unfold h; intros.
      rewrite undom in H11; auto. deHun.
      - rewrite uvinf; eauto. unfold f. rewrite fuprv,K1; auto.
        intro. apply H7. eapply H0; eauto.
      - rewrite domor in H11; auto. eins H11. rewrite uvinp; auto.
        appA2H H4. rewrite fuprv,K2; auto. apply MKT101. }
    elim H7. eapply subdom; eauto. appA2G. exists g[f]. appA2G.
  - rewrite MKT69a; auto.
Qed.

Lemma lem128 : ∀ {f g h}, Function f -> Function h
  -> Ordinal dom(f) -> Ordinal dom(h)
  -> (∀ x, Ordinal_Number x -> f[x] = g [f|(x)])
  -> (∀ x, Ordinal_Number x -> h[x] = g [h|(x)])
  -> h ⊂ f -> h = f.
Proof.
  intros. New (MKT110 H1 H2). deor.
  - New ((subdom H5) _ H6). destruct (MKT101 _ H7).
  - assert (Ordinal_Number dom(h)). { appA2G. }
    New (H3 _ H7). New (H4 _ H7). New (MKT101 dom(h)).
    apply MKT69a in H10. apply MKT69b in H6.
    rewrite fresub in H8; rewrite fresub in H9; auto.
    rewrite H8,<-H9,H10 in H6. elim MKT39; eauto.
  - apply MKT71; auto; intros. TF (x ∈ dom(h)).
    + apply subval; auto.
    + rewrite (@ MKT69a x); auto. rewrite <-H6 in H7.
      rewrite MKT69a; auto.
Qed.

Theorem MKT128b :  ∀ g, ∀ f, Function f /\ Ordinal dom(f)
    /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)])
  -> ∀ h, Function h /\ Ordinal dom(h)
    /\ (∀ x, Ordinal_Number x -> h[x] = g[h|(x)]) -> f = h.
Proof.
  intros. deand.
  assert (∀ u, u ∈ dom(f) -> f[u] = g[f|(u)]); intros.
  { apply H4; appA2G. eapply MKT111 in H5; eauto. }
  assert (∀ u, u ∈ dom(h) -> h[u] = g[h|(u)]); intros.
  { apply H2; appA2G. eapply MKT111 in H6; eauto. }
  destruct (MKT127 H H3 H5 H0 H1 H6); [symmetry|];
  eapply lem128; eauto.
Qed.

Fact EnEm : Ensemble Φ.
Proof.
  destruct AxiomVIII as [? [? []]]. eauto.
Qed.

Global Hint Resolve EnEm : core.

Fact powEm : pow(Φ) = [Φ].
Proof.
  eqext.
  - apply MKT38b,esube in H; subst; auto.
  - eins H. apply MKT38b; auto.
Qed.

(* Theo132 *)
Theorem MKT132 : ∀ x y, Integer x -> y ∈ x -> Integer y.
Proof.
  intros. destruct H. split; [eapply MKT111; eauto|].
  split; unfold Connect; intros.
  - apply H1; eapply H; eauto.
  - apply H in H0. apply H1; auto. eapply MKT28; eauto.
Qed.

(* Theo133 *)
Theorem MKT133 : ∀ {x y}, y ∈ R -> LastMember x E y
  -> y = PlusOne x.
Proof.
  intros. destruct H0. appA2H H. eqext.
  - appA2G. New H0. New H3.
    apply MKT111 in H0; apply MKT111 in H3; auto.
    New (MKT110 H0 H3); deor; auto.
    + destruct (H1 _ H5). appoA2G; rxo. appoA2G; rxo.
    + subst. right. eauto.
  - appA2H H3. destruct H4.
    + eapply H2; eauto.
    + eins H4.
Qed.

(* Theo134 *)
Theorem MKT134 : ∀ {x}, x ∈ ω -> (PlusOne x) ∈ ω.
Proof.
  intros. appA2H H. destruct H0. appA2G; [|split].
  - apply AxiomIV; auto.
  - assert (x ∈ R). { appA2G. }
    apply Lem123 in H2. appA2H H2; auto.
  - destruct H1. split; unfold Connect; intros.
    + eincus H3; eincus H4.
      * right. left. appoA2G. appoA2G.
      * left. appoA2G. appoA2G.
    + TF (x ∈ y).
      * exists x; split; auto; intros; intro.
        appoA2H H7. appoA2H H8. apply H3 in H6. eincus H6;
        [eapply MKT102|eapply MKT101]; eauto.
      * apply H2; auto. red; intros. New H6.
        apply H3 in H6. eincus H6. tauto.
Qed.

Global Hint Resolve MKT134 : core.

(* Theo135 *)
Theorem MKT135 : Φ ∈ ω /\ (∀ x, x ∈ ω -> Φ ≠ PlusOne x).
Proof.
  split; intros.
  - appA2G. split; red; split; try red; intros; try emf.
    elim H0. apply MKT27; auto.
  - intro. feine x. rewrite H0. appA2G.
Qed.

Theorem MKT135a : Φ ∈ ω.
Proof.
  appA2G. split; red; split; try red; intros; try emf.
  elim H0. apply MKT27; auto.
Qed.

Global Hint Resolve MKT135a : core.

Theorem MKT135b : ∀ x, x ∈ ω -> Φ ≠ PlusOne x.
Proof.
  intros; intro. feine x. rewrite H0. appA2G.
Qed.

(* Theo136 *)
Theorem MKT136 : ∀ x y, x ∈ ω -> y ∈ ω -> PlusOne x = PlusOne y
  -> x = y.
Proof.
  intros. appA2H H. appA2H H0. destruct H2,H3.
  rewrite <-MKT124,<-(MKT124 x), H1; auto; appA2G.
Qed.

(* Theo137 *)
Corollary Property_W : Ordinal ω.
Proof.
  split; red; unfold Included; intros.
  - appA2H H. appA2H H0. destruct H1,H2. apply Lemma113; auto.
  - appA2H H. appA2G. eapply MKT132; eauto.
Qed.

Global Hint Resolve Property_W : core.

Theorem MKT137 : ∀ x, x ⊂ ω -> Φ ∈ x
  -> (∀ u, u ∈ x -> (PlusOne u) ∈ x) -> x = ω.
Proof.
  intros. Absurd.
  assert (∃ y, FirstMember y E (ω ~ x)).
  { apply (@ MKT107 ω); auto; red; intros.
    - appA2H H3; tauto.
    - apply H2. eqext; auto. Absurd.
      feine z. rewrite <-H3; auto. }
  destruct H3 as [y []]. appA2H H3.
  destruct H5. appA2H H6. appA2H H5.
  assert (∃ u, FirstMember u E⁻¹ y).
  { apply H8; auto. intro. subst. contradiction. } 
  destruct H9 as [u]. inversion H9 as [].
  assert (u ∈ x).
  { Absurd. eapply MKT132 in H8; eauto.
  destruct (H4 u); [|appoA2G]. appA2G; split; appA2G. }
  destruct H8. eapply MKT133 in H9; [|appA2G]. subst.
  apply H1 in H12. elim H7; auto.
Qed.

(* Theo138 *)
Theorem MKT138 : ω ∈ R.
Proof.
  appA2G. destruct (AxiomVIII) as [? [? []]].
  eapply MKT33; eauto. apply MKT30. apply MKT137; intros.
  - red; intros. appA2H H2; tauto.
  - appA2G.
  - appA2H H2. destruct H3. New (MKT134 H3). appA2G.
Qed.

(* Mathematical Induction *)
Theorem MiniMember_Principle : ∀ S, S ⊂ ω -> S ≠ Φ
  -> ∃ a, a ∈ S /\ (∀ c, c ∈ S -> a ≼ c).
Proof.
  intros. apply (MKT107 Property_W) in H0 as [a []]; auto.
  exists a; split; auto; intros. unfold LessEqual.
  New H0. apply H in H0. eapply MKT111 in H0; eauto.
  New H2. apply H in H2. eapply MKT111 in H2; eauto.
  New (MKT110 H0 H2). deor; auto. destruct (H1 c H4). appoA2G; rxo.
Qed.

Theorem Mathematical_Induction : ∀ (P :Class -> Prop), P Φ
  -> (∀ k, k ∈ ω -> P k -> P (PlusOne k)) -> (∀ n, n ∈ ω -> P n).
Proof.
  intros. assert (\{λ x, x ∈ ω /\ P x \} = ω).
  { apply MKT137; try red; intros.
    - appA2H H2; tauto.
    - appA2G.
    - appA2H H2. destruct H3. appA2G. }
  rewrite <-H2 in H1. appA2H H1; tauto.
Qed.

Ltac MI x := apply Mathematical_Induction with (n:=x); auto; intros.

Fact caseint : ∀ {x}, x ∈ ω
  -> x = Φ \/ (∃ v, v ∈ ω /\ x = PlusOne v).
Proof.
  intros. MI x. destruct H1 as [|[? []]]; subst; eauto.
Qed.

Theorem The_Second_Mathematical_Induction : ∀ (P: Class -> Prop),
  P Φ -> (∀ k, k ∈ ω -> (∀ m, m ≺ k -> P m) -> P k)
  -> (∀ n, n ∈ ω -> P n).
Proof.
  intros. apply H0; auto; intros. generalize dependent m. MI n.
  - red in H2. emf.
  - eincus H4; eauto.
Qed.

(* Theo140 *)
Fact f2Pf : ∀ {f} P, let g := \{\ λ u v, v = f[P u] \}\ in
  Function f -> (∀ h, Ensemble h -> g[h] = f[P h]).
Proof.
  intros. eqext.
  - appA2G. intros. appA2H H2. appA2H H1. apply H4. appA2G.
    apply Property_Fun in H3; auto. subst. appoA2G.
  - appA2G. intros. appA2H H2. appA2H H1. apply H4. appA2G.
    appoA2H H3. subst. apply Property_Value,MKT69b'; auto.
Qed.

Fact c2fp : ∀ {x c g P f}, Ensemble x -> dom(c) = μ ~ [Φ]
  -> (∀ x, x ∈ dom(c) -> c[x] ∈ x)
  -> (∀ h, Ensemble h -> g[h] = c[P h])
  -> (∀ x, Ordinal_Number x -> f[x] = g[f|(x)])
  -> Function f -> Ordinal dom(f)
  -> (∀ u, u ∈ dom(f) -> Ensemble (P (f|(u)))
    -> f[u] ∈ (P (f|(u)))).
Proof.
  intros. assert (Ordinal_Number u).
  { appA2G. eapply MKT111; eauto. }
  assert (Ensemble (f|(u))).
  { apply MKT75; [apply MKT126a|rewrite MKT126b]; auto.
    apply (MKT33 u); eauto. red; intros. appA2H H9. tauto. }
  rewrite H3,H2; auto. apply H1. rewrite H0. appA2G. split; auto.
  appA2G. intro. eins H10. New H6.
  apply MKT69b in H6. rewrite H3,H2 in H6; auto.
  apply MKT69b' in H6. rewrite H10,H0 in H6.
  appA2H H6. destruct H12. appA2H H13. apply H14; auto.
Qed.

Theorem MKT140 : ∀ x, Ensemble x
  -> ∃ f, Function1_1 f /\ ran(f) = x /\ Ordinal_Number dom(f).
Proof.
  intros. destruct AxiomIX as [c [[]]].
  New (f2Pf (λ u, x ~ ran(u)) H0). simpl in H3.
  set (g := \{\ λ u v, v = c[x ~ ran(u)] \}\) in *.
  destruct (MKT128a g) as [f]. deand.
  assert (∀ u, u ∈ dom(f) -> f[u] ∈ (x ~ ran(f|(u)))).
  { intros. apply (c2fp H H2 H1 H3 H6 H4 H5); auto.
    apply (MKT33 x); auto. red; intros. appA2H H8. tauto. }
  assert (Function1_1 f).
  { split; auto; split; try red; intros.
    - PP H8 a b; eauto.
    - appoA2H H8. appoA2H H9. New H10. New H11.
      apply Property_Fun in H10; apply Property_Fun in H11; auto.
      subst. New H12. New H13.
      apply Property_dom in H12; apply Property_dom in H13.
      New (H7 _ H12). appA2H H15. destruct H16. appA2H H17.
      New (H7 _ H13). appA2H H19. destruct H20. appA2H H21. New H13.
      apply MKT111 in H12; apply MKT111 in H13; auto.
      New (MKT110 H12 H13). deor; auto.
      + elim H22; appA2G. exists y. appA2G; rxo.
        rewrite H11 in H10. split; auto. appoA2G.
      + elim H18; appA2G. exists z. appA2G; rxo.
        split; auto. appoA2G. }
  assert (ran(f) ⊂ x).
  { red; intros. appA2H H9. destruct H10. New H10.
    apply Property_Fun in H11; subst; auto.
    apply Property_dom in H10. apply H7 in H10. appA2H H10; tauto. }
  assert (Ordinal_Number dom(f)).
  { destruct H8. appA2G. rewrite deqri. apply AxiomV; auto.
    rewrite <-reqdi. eapply MKT33; eauto. }
  exists f; deandG; auto. apply MKT27; split; auto.
  red; intros. New H10. appA2H H12. apply MKT75 in H12; auto.
  apply H6 in H10. rewrite fresub in H10; auto. Absurd.
  rewrite MKT69a, H3 in H10; [|auto|apply MKT101].
  elim MKT39. rewrite H10. exists (x ~ ran(f)). apply H1.
  assert (Ensemble (x ~ ran(f))). { apply (MKT33 x); eauto. }
  rewrite H2. apply setminP; auto. intro. eins H16.
  feine z; rewrite <-H16; auto.
Qed.

(* Theo142 *)
Theorem MKT142 : ∀ n, Nest n -> (∀ m, m ∈ n -> Nest m)
  -> Nest (∪n).
Proof.
  intros; red; intros. appA2H H1. appA2H H2. unfold Nest in H0.
  rdeHex. destruct (H _ _ H5 H6); eauto.
Qed.

(* Theo143 *)
Theorem MKT143 : ∀ x, Ensemble x -> ∃ n, (Nest n /\ n ⊂ x)
  /\ (∀ m, Nest m -> m ⊂ x -> n ⊂ m -> m = n).
Proof.
  intros. destruct AxiomIX as [c [[]]].
  New (f2Pf (λ u, \{ λ m, Nest m /\ m ⊂ x
    /\ (∀ p, p ∈ ran(u) -> p ⊂ m /\ p <> m) \}) H0). simpl in H3.
  set (g := \{\ λ u v, v = c[\{ λ m, Nest m /\ m ⊂ x
    /\ (∀ p, p ∈ ran(u) -> p ⊂ m /\ p <> m) \}] \}\) in *.
  destruct (MKT128a g) as [f]. deand.
  assert (∀ u, Ensemble \{ λ m, Nest m /\ m ⊂ x
    /\ (∀ p, p ∈ ran(f|(u)) -> p ⊂ m /\ p <> m) \}) as G; intros.
  { apply (MKT33 pow(x)); [apply MKT38a; auto|].
    red; intros. appA2H H7. apply MKT38b; tauto. }
  assert (∀ u, u ∈ dom(f) -> Nest f[u] /\ f[u] ⊂ x ).
  { intros. apply (c2fp H H2 H1 H3 H6 H4 H5) in H7;
    [appA2H H7; tauto|auto]. }
  assert (∀ u v, u ∈ dom(f) -> v ∈ dom(f) -> u ∈ v
    -> f[u] ⊂ f[v] /\ f[u] <> f[v]); intros.
  { apply (c2fp H H2 H1 H3 H6 H4 H5) in H9; auto. appA2H H9. deand.
    apply H13. apply Property_Value in H8; auto. appA2G; ope.
    exists u. appA2G. split; auto. appoA2G; split; auto.
    apply MKT19; ope. }
  exists (∪ran(f)). deandG; try red; intros.
  - appA2H H9. appA2H H10. rdeHex.
    appA2H H13. appA2H H14. destruct H15,H16. New H15. New H16.
    apply Property_Fun in H15; apply Property_Fun in H16; subst;
    auto. apply Property_dom in H17; apply Property_dom in H18.
    New H17. New H18. destruct (H7 _ H17),(H7 _ H18). deand.
    apply MKT111 in H17; apply MKT111 in H18; auto.
    New (MKT110 H17 H18). deor; subst; auto.
    + destruct (H8 _ _ H15 H16 H23); auto.
    + destruct (H8 _ _ H16 H15 H23); auto.
  - appA2H H9. rdeHex. appA2H H11. destruct H12.
    New H12. apply Property_Fun in H12; subst; auto.
    apply Property_dom in H13. eapply H7; eauto.
  - assert (Function f⁻¹).
    { split; try red; intros.
      - PP H12 a b; eauto.
      - appoA2H H12. appoA2H H13. New H14. New H15.
        apply Property_Fun in H14; apply Property_Fun in H15; auto.
        subst. apply Property_dom in H16.
        apply Property_dom in H17. New H16. New H17.
        apply MKT111 in H14; apply MKT111 in H18; auto.
        New (MKT110 H14 H18). deor; auto.
        + New (H8 _ _ H16 H17 H19). destruct H20,H21; auto.
        + New (H8 _ _ H17 H16 H19). destruct H20,H21; auto. }
    assert (ran(f) ⊂ pow(x)).
    { red; intros. appA2H H13. destruct H14. New H14.
      apply Property_Fun in H14; subst; auto.
      apply Property_dom in H15. apply H7 in H15. destruct H15.
      apply MKT38b; auto. }
    assert (Ordinal_Number dom(f)).
    { appA2G. rewrite deqri. apply AxiomV; auto. rewrite <-reqdi.
      apply (MKT33 pow(x)); auto. apply MKT38a; auto. }
    assert (Ensemble f). { apply MKT75; auto. appA2H H14; auto. }
    Absurd. apply H6 in H14. rewrite frebig,H3 in H14; auto.
    rewrite MKT69a in H14; [|apply MKT101]. symmetry in H14.
    apply MKT69a' in H14. elim H14. rewrite H2.
    rewrite <-(fresub f f); auto. apply setminP; auto.
    intro. eins H17. feine m. rewrite <-H17, frebig; auto.
    appA2G; [apply (MKT33 x)|]; deandG; auto. split; red; intros.
    + apply H11. appA2G.
    + subst. elim H16. apply MKT27; split; [apply MKT32|]; auto.
Qed.

Fact eqvp : ∀ {x y}, Ensemble y -> x ≈ y -> Ensemble x.
Proof.
  intros. destruct H0 as [? [[] []]]. deand. subst.
  rewrite reqdi in H. rewrite deqri. apply AxiomV; auto.
Qed.

(* Theo145 x≈x *)
Theorem MKT145 : ∀ x, x ≈ x.
Proof.
  intros. exists (\{\ λ u v, u ∈ x /\ u = v \}\). deandG.
  - repeat split; auto; intros.
    + appoA2H H. appoA2H H0. destruct H1,H2. subst. auto.
    + red; intros. PP H a b. eauto.
    + appoA2H H. appoA2H H0. appoA2H H1. appoA2H H2.
      destruct H3,H4. subst. auto.
  - eqext.
    + appA2H H. destruct H0. appoA2H H0. tauto.
    + appA2G. exists z. appoA2G; rxo.
  - eqext.
    + appA2H H. destruct H0. appoA2H H0. destruct H1. subst; auto.
    + appA2G. exists z. appoA2G; rxo.
Qed.

Global Hint Resolve MKT145 : core.

(* Theo146 if x≈y, then y≈x *)
Theorem MKT146 : ∀ {x y}, x ≈ y -> y ≈ x.
Proof.
  intros. destruct H as [f]. deand. exists f⁻¹. deandG.
  - destruct H. inversion H. split; auto. rewrite MKT61; auto.
  - rewrite <-reqdi; auto.
  - rewrite <-deqri; auto.
Qed.

(* Theo147 if x≈y and y≈z, then x≈z *)
Theorem MKT147 : ∀ y x z, x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  intros. destruct H as [f1], H0 as [f2]. deand.
  exists (f2 ∘ f1). deandG; subst.
  - destruct H,H0. split; [|rewrite MKT62]; apply MKT64; auto.
  - eqext.
    + appA2H H2. destruct H3. appoA2H H3. destruct H4,H4.
      eapply Property_dom; eauto.
    + appA2H H2. destruct H3. New (Property_ran H3).
      rewrite <-H1 in H4. appA2H H4. destruct H5.
      appA2G. exists x0. appoA2G. xo; ope.
  - eqext.
    + appA2H H2. destruct H3. appoA2H H3. destruct H4,H4.
      eapply Property_ran; eauto.
    + appA2H H2. destruct H3. New (Property_dom H3).
      rewrite H1 in H4. appA2H H4. destruct H5.
      appA2G. exists x0. appoA2G. xo; ope.
Qed.

(* Theo150 E well-orders C *)
Theorem MKT150 : WellOrdered E C.
Proof.
  split; try red; intros.
  - appA2H H. appA2H H0. destruct H1,H2. appA2H H1. appA2H H2.
    apply Lemma113; auto.
  - apply (wosub R E y); auto; [apply (MKT107 MKT113a)|].
    red; intros. apply H in H1. appA2H H1. destruct H2.
    appA2H H2. appA2G.
Qed.

(* Theo152 P is a function whose domain is μ and range is C *)
Theorem MKT152a : Function P.
Proof.
  unfold P; split; intros; auto.
  appoA2H H. appoA2H H0. destruct H1,H2. appA2H H3. appA2H H4.
  destruct H5,H6. New H5. New H6. appA2H H5. appA2H H6.
  apply MKT146 in H2. eapply MKT147 in H1; eauto.
  New (MKT110 H11 H12); deor; auto.
  - destruct (H8 y); auto.
  - apply MKT146 in H1. destruct (H7 z); auto.
Qed.

Global Hint Resolve MKT152a : core.

Theorem MKT152b : dom(P) = μ.
Proof.
  eqext; eauto. New H. apply MKT19, MKT140 in H as [f]. deand.
  set (S := \{ λ x, x ≈ z /\ Ordinal x \}).
  assert (∃ z, FirstMember z E S).
  { apply (wosub R E S); auto; [apply (MKT107 MKT113a)|..].
    - red; intros. appA2H H3. destruct H4. appA2G.
    - appA2H H2. apply NEexE. exists dom(f). appA2G.
      unfold Equivalent; eauto. }
  destruct H3 as [w []]. appA2H H3. destruct H5. appA2G.
  exists w. appoA2G. apply MKT146 in H5. split; auto.
  appA2G; split; red; intros; [appA2G|]. apply (H4 y); [|appoA2G].
  appA2H H7. eapply MKT147, MKT146 in H9; eauto. appA2G.
Qed.

Theorem MKT152c : ran(P) = C.
Proof.
  eqext; appA2H H.
   + destruct H0. appoA2H H0. tauto.
   + appA2G. exists z. appoA2G. split; [auto|appA2G].
Qed.

(* Corollary of Definition151 (in mk_structure.v) *)
Corollary Property_PClass : ∀ {x}, Ensemble x -> P [x] ∈ C.
Proof.
  intros. rewrite <-MKT152c. apply Property_dm; auto.
  rewrite MKT152b; auto.
Qed.

Global Hint Resolve Property_PClass : core.

(* Theo153 if x is a set, then P[x] ≈ x *)
Theorem MKT153 : ∀ {x}, Ensemble x -> P[x] ≈ x.
Proof.
  intros. apply MKT19 in H. rewrite <-MKT152b in H.
  apply Property_Value in H; auto. appoA2H H. destruct H0.
  apply MKT146; auto.
Qed.

Global Hint Resolve MKT153 : core.

Fact pveqv : ∀ x y, Ensemble y -> P[x] = y -> x ≈ y.
Proof.
  intros. rewrite <-H0. apply MKT146,MKT153.
  rewrite <-H0 in H. apply MKT19,MKT69b' in H; eauto.
Qed.

Fact carE : ∀ {x}, P[x] = Φ -> x = Φ.
Proof.
  intros. eqE. apply pveqv in H as [f [[][]]]; auto. subst.
  feine f[z]. rewrite <-H3. apply Property_dm; auto.
Qed.

(* Theo154 if x and y are sets, then P(x)=P(y) iff x≈y *)
Theorem MKT154 : ∀ x y, Ensemble x -> Ensemble y
  -> (P[x] = P[y] <-> x ≈ y).
Proof.
  split; intros.
  - New (MKT153 H0). apply (MKT147 P[y]); auto.
    rewrite <-H1. apply MKT146,MKT153; auto.
  - assert ([x,P[y]] ∈ P).
    { appoA2G; split; auto. eapply MKT147; eauto.
      apply MKT146, MKT153; auto. }
    apply Property_Fun in H2; auto.
Qed.

(* Theo155 P[P[x]] = P[x] *)
Theorem MKT155 : ∀ x, P[P[x]] = P[x].
Proof.
  intros. TF (x ∈ dom(P)).
  - apply MKT154; eauto. apply MKT19, MKT69b; auto.
  - rewrite (@ MKT69a x); auto. apply MKT69a.
    intro. apply MKT39; eauto.
Qed.

(* Theo156 x∈C iff x is a set and P[x]=x *)
Theorem MKT156 : ∀ x, (Ensemble x /\ P[x] = x) <-> x∈C.
Proof.
  split; intros.
  - destruct H. rewrite <-H0,<-MKT152c.
    apply Property_dm; auto. rewrite MKT152b; auto.
  - split; eauto. appA2H H. destruct H0. appA2H H0.
    apply Property_PClass in H. appA2H H. destruct H3. appA2H H3.
    New (MKT110 H5 H2); deor; auto.
    + destruct (H1 P[x]); auto; [appA2G|]. apply MKT146; auto.
    + destruct (H4 x); auto. appA2G.
Qed.

(* Theo157 if y∈R and x⊂y, 则P(x)≼y *)
Theorem MKT157 : ∀ x y, y ∈ R -> x ⊂ y -> P[x] ≼ y.
Proof.
  intros. appA2H H. New (MKT33 _ _ H H0).
  assert (WellOrdered E x).
  { eapply wosub; eauto. apply MKT107, H1. }
  New (MKT107 MKT113a). New (Property_PClass H2).
  destruct (MKT100 H3 H4 H2 MKT113b) as [f]. deand. subst.
  red in H7. deand. apply MKT96 in H9 as [[_]].
  assert (On f⁻¹ ran(f)). { red. rewrite reqdi; auto. }
  assert (To f⁻¹ R).
  { red; split; auto. rewrite <-deqri. red; intros.
    appA2G. eapply MKT111; eauto. }
  New (MKT94 H11 H12 H13 H14). 
  assert (ran(f) ⊂ y).
  { red; intros. einr H16. New H17. apply H11 in H18.
    apply H15 in H17. rewrite f11iv in H17; auto.
    appA2H H18. New (H0 _ H16). apply MKT111 in H20; auto.
    New (MKT110 H20 H19). deor.
    - elim H17; appoA2G.
    - apply H0 in H16. eapply H1; eauto.
    - rewrite <-H21; auto. } apply MKT114 in H11.
  assert (ran(f) ≼ y).
  { red. TF (ran(f) = y); auto. left.
    eapply MKT108; auto. apply H11. }
  appA2H H5. destruct H18. appA2H H18.
  assert (dom(f) ≈ ran(f)).
  { red; exists f; split; split; auto. }
  New (MKT110 H1 H20). deor; red; auto.
  assert (ran(f) ∈ P[dom(f)]).
  { destruct H17; subst; auto. eapply H20; eauto. }
  destruct (H19 ran(f)); auto; [appA2G|].
  New (MKT153 H2). eapply MKT147; eauto.
Qed.

(* Theo158 if y∈R and x⊂y, then P[x]≼P[y] *)
Theorem MKT158 : ∀ {x y}, x ⊂ y -> P[x] ≼ P[y].
Proof.
  intros. TF (Ensemble y).
  - assert (Ensemble x). { apply MKT33 in H; auto. }
    New (MKT146 (MKT153 H0)). destruct H2 as [f [[] []]]. subst.
    assert (ran(f|(x)) ⊂ P[dom(f)]).
    { red; intros. rewrite <-H5. appA2H H4. destruct H6.
      appA2H H6. destruct H7. eapply Property_ran; eauto. }
    assert (x ≈ ran(f|(x))).
    { exists (f|(x)); deandG; [split|..]; auto.
      - apply MKT126a; auto.
      - split; try red; intros.
        + PP H6 a b. eauto.
        + appoA2H H6. appoA2H H7. appA2H H8. appA2H H9.
          destruct H10,H11. eapply H3; apply invp1; eauto.
      - rewrite MKT126b; auto. apply MKT30; auto. }
    New (Property_PClass H0). appA2H H7. destruct H8. appA2H H8.
    New (MKT33 _ _ H7 H4). apply MKT154 in H6; auto.
    apply MKT157 in H4; [|appA2G]. rewrite <-H6 in H4; auto.
  - TF (Ensemble x).
    + rewrite (@ MKT69a y); [|intro; eauto]. left.
      apply MKT69b. rewrite MKT152b; auto.
    + rewrite MKT69a,MKT69a; red; auto; intro; eauto.
Qed.

(* Theo159 if x and y are sets, u⊂x, v⊂y, x≈v and y≈u, then x≈y *)
Theorem MKT159 : ∀ x y u v, Ensemble x -> Ensemble y
  -> u ⊂ x -> v ⊂ y -> x ≈ v -> y ≈ u -> x ≈ y.
Proof.
  intros. New (MKT158 H1). New (MKT158 H2).
  apply MKT33 in H1; apply MKT33 in H2; auto.
  apply MKT154 in H3; apply MKT154 in H4; auto.
  rewrite <-H3 in H6. rewrite <-H4 in H5. apply MKT154; auto.
  apply Property_PClass in H; apply Property_PClass in H0.
  appA2H H. appA2H H0. destruct H7,H8. appA2H H7. appA2H H8.
  apply MKT27; split; apply MKT118; auto.
Qed.

(* Theo160 if f is function and a set, then P(domain f) ≼ P(range f) *)
Theorem MKT160 : ∀ {f}, Function f -> Ensemble f -> P[ran(f)] ≼ P[dom(f)].
Proof.
  intros. destruct AxiomIX as [c [[]]].
  assert (∀ y, y ∈ ran(f) -> \{ λ x, y = f[x] \} ∈ dom(c)).
  { intros. assert (Ensemble \{ λ x, y = f[x] \}).
    { New (fdme H H0). apply (MKT33 dom(f)); auto. red; intros.
      appA2H H6. rewrite H7 in H4. apply MKT69b'; eauto. }
    rewrite H3. appA2G. split; auto. appA2G. intro.
    eins H6. einr H4. feine x. rewrite <-H6. appA2G. }
  set (g := \{\ λ u v, u ∈ ran(f) /\ v = c[\{ λ x, u = f[x] \}] \}\).
  assert (dom(g) = ran(f)).
  { eqext; appA2H H5; destruct H6.
    - appoA2H H6; tauto.
    - New H6. apply Property_Fun in H6; subst; auto.
      apply Property_ran in H7. appA2G.
      exists c[\{ λ y, f[x] = f[y] \}]. appoA2G. rxo. }
  assert (ran(g) ⊂ dom(f)).
  { red; intros. appA2H H6. destruct H7. appoA2H H7. destruct H8.
    subst. New H8. apply H4,H2 in H8. appA2H H8. rewrite H10 in H9.
    apply Property_Value',Property_dom in H9; auto. }
  assert (dom(g) ≈ ran(g)).
  { exists g; deandG; auto; repeat split;
    unfold g; auto; try red; intros.
    - appoA2H H7. appoA2H H8. destruct H9,H10. subst; auto.
    - PP H7 a b; eauto.
    - appoA2H H7. appoA2H H8. appoA2H H9. appoA2H H10.
      destruct H11,H12. apply H4,H2 in H11; apply H4,H2 in H12.
      subst. appA2H H11. appA2H H12. rewrite H13,H15,H14; auto. }
  apply MKT158 in H6. New (frne H H0). rewrite <-H5 in H8.
  inversion H7 as [? [[]]]. deand. New H8. rewrite <-H11 in H13.
  apply AxiomV in H13; auto. rewrite H12 in H13.
  apply MKT154 in H7; auto. rewrite <-H7,H5 in H6; auto.
Qed.

(* Theo161 if x is a set, then P[x] ≺ P[pow(x)] *)
Theorem MKT161 : ∀ {x}, Ensemble x -> P[x] ≺ P[pow(x)].
Proof.
  intros. set (g := \{\ λ u v, u∈x /\ v = [u] \}\).
  assert (ran(g) = \{ λ v, ∃ u, u ∈ x /\ v = [u] \}).
  { eqext.
    - appA2H H0. destruct H1. appoA2H H1.
      destruct H2; subst. appA2G.
    - appA2H H0. rdeHex. subst. appA2G. exists x0. appoA2G. }
  assert(x ≈ \{ λ v, ∃ u, u ∈ x /\ v = [u] \}).
  { red; exists \{\ λ u v, u ∈ x /\ v = [u] \}\.
    repeat split; auto; try red; try eqext; intros.
    - appoA2H H1. appoA2H H2. destruct H3,H4. subst; auto.
    - PP H1 a b. eauto.
    - appoA2H H1. appoA2H H2. appoA2H H3. appoA2H H4.
      destruct H5,H6. subst. apply MKT41; eauto.
      rewrite <-H8. appA2G.
    - appA2H H1. destruct H2. appoA2H H2; tauto.
    - appA2G. exists [z]. appoA2G; rxo. } rewrite <-H0 in H1.
  assert (ran(g) ⊂ pow(x)).
  { rewrite H0; red; intros. appA2H H2. rdeHex.
    subst. apply MKT38b; auto. red; intros. eins H4. }
  New (MKT38a H). New H3. eapply MKT33 in H3; eauto.
  apply MKT158 in H2. apply MKT154 in H1; auto.
  rewrite <-H1 in H2. destruct H2; red; auto.
  apply MKT154 in H2; auto. destruct H2 as [f [[]]]. deand.
  assert (\{ λ v, v ∈ x /\ v ∉ f[v] \} ∈ ran(f)).
  { rewrite H7. apply MKT38b; auto. red; intros. appA2H H8. tauto. }
  einr H8. TF (x0 ∈ f[x0]); New H6.
  - rewrite <-H10 in H6. appA2H H6. destruct H12. elim H13; auto.
  - elim H6. rewrite <-H10. appA2G.
Qed.

(* Theo162 C is not a set *)
Theorem MKT162 : ~ Ensemble C.
Proof.
  intro. apply AxiomVI in H. New H. apply MKT161 in H0.
  apply MKT38a,Property_PClass,MKT32 in H as [? _].
  apply MKT158 in H. rewrite MKT155 in H. destruct H.
  - eapply MKT102; eauto.
  - rewrite H in H0. eapply MKT101; eauto.
Qed.

(* Theo163 if x,y∈ω and x+1≈y+1, then x≈y *)
Lemma Lemma163a : ∀ {x y}, Ensemble x -> ~ x ∈ y
  -> y = (y ∪ [x]) ~ [x].
Proof.
  intros; eqext.
  - apply setminP; [appA2G|]. intro. eins H2.
  - apply setminp in H1 as []. deHun; tauto.
Qed.

Lemma Lemma163b : ∀ {x y}, x ∈ y -> y = (y ~ [x]) ∪ [x].
Proof.
  intros; eqext.
  - appA2G. TF (z ∈ [x]); auto.
  - deHun; [appA2H H0; tauto|eins H0].
Qed.

Lemma Lemma163c : ∀ {x y z}, x ~ y ~ z = x ~ z ~ y.
Proof.
  intros. unfold Setminus. now rewrite MKT7',MKT7',(MKT6' ¬y).
Qed.

Theorem MKT163 : ∀ x y, x∈ω -> y∈ω -> (PlusOne x) ≈ (PlusOne y)
  -> x ≈ y.
Proof.
  intros. destruct H1 as [f [? []]].
  assert (x ∈ dom(f)). { rewrite H2. appA2G. }
  assert (y ∈ ran(f)). { rewrite H3. appA2G. }
  appA2H H4. appA2H H5. destruct H6,H7. TF (x = x1).
  - eapply H1 in H6; eauto. subst. exists (f ~ [[x1,y]]). deandG.
    + apply f11pa; auto.
    + destruct H1. rewrite dos1; auto. rewrite H2. unfold PlusOne.
      rewrite <-Lemma163a; eauto. apply MKT101.
    + destruct H1. rewrite ros1; auto. rewrite H3. unfold PlusOne.
      rewrite <-Lemma163a; eauto. apply MKT101.
  - exists ((f ~ [[x,x0]] ~ [[x1,y]]) ∪ [[x1,x0]]). deandG.
    + destruct (f11pa H1 H6). apply f11pb; ope.
      * apply f11pa; [apply f11pa; auto|]. apply setminP; auto.
        intro. pins H11; ope.
      * rewrite dos1; ope; auto.
        { destruct H1. rewrite dos1; auto. intro.
          apply setminp in H12 as []. apply H13; eauto. }
        { apply setminP; auto. intro. pins H11; ope. }
      * rewrite ros1; ope; auto.
        { destruct H1. rewrite ros1; auto. intro.
          apply setminp in H12 as []. apply setminp in H12 as [].
          apply H14; eauto. }
        { apply setminP; auto. intro. pins H11; ope. }
    + rewrite undom,domor; ope. rewrite dos1.
      * destruct H1. rewrite <-Lemma163b, dos1; auto. rewrite H2.
      unfold PlusOne. rewrite <-Lemma163a; eauto. apply MKT101.
      rewrite dos1; auto. apply setminP; auto.
      eapply Property_dom; eauto. intro. eins H10.
      * apply f11pa; auto.
      * apply setminP; auto. intro. pins H9; ope.
    + rewrite unran,ranor; ope. rewrite ros1.
      * destruct H1. rewrite ros1; auto. rewrite Lemma163c.
        rewrite <-Lemma163b,H3.
        unfold PlusOne. rewrite <-Lemma163a; eauto. apply MKT101.
        apply setminP; auto.
        eapply Property_ran; eauto. intro. eins H10.
        apply H8. eapply H9; apply invp1; eauto.
      * apply f11pa; auto.
      * apply setminP; auto. intro. pins H9; ope.
Qed.

(* Theo164 ω ⊂ C *)
Theorem MKT164 : ω ⊂ C.
Proof.
  New MKT113a. New MKT138. red; intros. MI z.
  - appA2G. split; [appA2G|intros; red in H3; emf]. New MKT135a.
    apply MKT111 in H1; apply MKT111 in H2; auto.
  - appA2H H3. destruct H4. appA2H H4.
    assert ((PlusOne k) ∈ ω). { apply MKT134; auto. }
    appA2G. split; red; intros.
    + appA2G. apply MKT111 in H0; apply MKT111 in H7; auto. 
    + assert (y ∈ ω). { appA2H H7. appA2G. eapply MKT132; eauto. }
      destruct (caseint H11) as [?|[n []]]; subst.
      * destruct H10 as [f [[] []]]. feine f[k]. rewrite <-H14.
        apply Property_dm; auto. rewrite H13. appA2G.
      * apply MKT163 in H10; auto. destruct (H5 n); auto.
        { appA2G. apply MKT111 in H0; apply MKT111 in H12; auto. }
        { appA2H H9. deor.
          - eapply H6; eauto. appA2G.
          - eins H13. appA2G. }
Qed.

(* Theo165 ω∈C *)
Theorem MKT165 : ω ∈ C.
Proof.
  New MKT138. appA2G. split; auto. intros. intro.
  New (MKT134 H1). New H. appA2H H.
  assert (y ⊂ PlusOne y). { red; intros. appA2G. }
  assert (PlusOne y ⊂ ω).
  { red; intros. apply MKT134 in H1.
    apply MKT111 in H1; auto. eapply H5; eauto. }
  apply MKT158 in H6. apply MKT158 in H7.
  apply MKT154 in H2; eauto.
  assert (P[PlusOne y] = P[y]).
  { destruct H6,H7; auto; rewrite H2 in *.
    - destruct (MKT102 _ _ H6 H7).
    - rewrite H7 in H6. destruct (MKT101 _ H6). }
  apply MKT164 in H3. appA2H H3. destruct H9.
  apply MKT154 in H8; eauto. destruct (H10 y); auto. appA2G.
Qed.

Corollary Property_Finite : ∀ {x}, Finite x -> Ensemble x.
Proof.
  intros. assert (Ensemble P[x]) by eauto.
  apply MKT19,MKT69b' in H0; eauto.
Qed.

Lemma finsub : ∀ {A B}, Finite A -> B ⊂ A -> Finite B.
Proof.
  unfold Finite; intros. destruct (MKT158 H0).
  - New MKT138. appA2H H2. eapply H3; eauto.
  - rewrite H1; auto.
Qed.

Lemma finsin : ∀ z, Ensemble z -> Finite ([z]).
Proof.
  intros. assert ([z] ≈ [Φ]).
  { exists ([[z,Φ]]). deandG.
    - split; [|rewrite siv]; try apply opisf; auto.
    - apply domor; auto.
    - apply ranor; auto. }
  apply MKT154 in H0; auto. New (MKT134 MKT135a).
  unfold PlusOne in H1. rewrite MKT17 in H1. New H1. red.
  apply MKT164,MKT156 in H1 as []. rewrite H0,H3; auto.
Qed.

Lemma finue : ∀ {x z}, Finite x -> Ensemble z -> ~ z ∈ x
  -> P[x ∪ [z]] = PlusOne P[x].
Proof.
  intros. New (Property_Finite H). New (MKT153 H2). New H3.
  apply eqvp in H3; auto. apply MKT146 in H4 as [f [? []]].
  red in H. New (MKT134 H). apply MKT164 in H7.
  symmetry. apply Property_Fun; auto. appoA2G; [|split; auto].
   - rxo. apply AxiomIV; auto.
   - exists (f ∪ [[z,P[x]]]). deandG; subst.
     + apply f11pb; auto. rewrite H6. apply MKT101.
     + rewrite undom,domor; auto.
     + rewrite unran,ranor,H6; auto.
Qed.

Fact finse : ∀ f {y u z}, P[y] = PlusOne u -> u ∈ ω -> Function f
  -> Function f⁻¹ -> dom(f) = y -> ran(f) = PlusOne u -> z ∈ y
  -> P[y ~ [z]] = u.
Proof.
  intros. assert (Finite (y ~ [z])).
  { apply MKT134 in H0. rewrite <-H in H0.
    eapply finsub; eauto. }
  rewrite (Lemma163b H5), finue in H; eauto.
  - apply MKT136 in H; auto.
  - intro. apply setminp in H7 as []. apply H8; eauto.
Qed.

(* Theo167  x is finite iff
            there exists r such that r well-orders x and r⁻¹ well-orders x *)
Lemma lem167a : ∀ r x f, WellOrdered r P[x] -> Function1_1 f -> dom(f) = x
  -> ran(f) = P[x] -> WellOrdered \{\ λ u v, Rrelation f[u] r f[v] \}\ x.
Proof.
  intros. destruct H,H0. split; try red; intros.
  - subst. New H5. New H6.
    apply Property_dm in H5; apply Property_dm in H6; auto.
    rewrite H2 in H5,H6. New (H _ _ H5 H6). deor.
    + left. appoA2G; rxo.
    + right; left. appoA2G; rxo.
    + right; right. apply (f11inj f); auto.
  - assert (ran(f|(y)) ⊂ P [x]).
    { red; intros. rewrite <-H2. appA2H H7. destruct H8.
      appA2H H8. destruct H9. eapply Property_ran; eauto. }
    assert (ran(f|(y)) ≠ Φ).
    { NEele H6. apply NEexE. New H6. apply H5 in H6.
      rewrite <-H1 in H6. appA2H H6. destruct H9.
      exists x1. appA2G; ope. exists x0. appA2G. split; auto.
      appoA2G. split; eauto. apply MKT19; ope. }
    destruct (H3 _ H7 H8) as [? []]. appA2H H9. destruct H11.
    appA2H H11. destruct H12. appoA2H H13. destruct H14.
    exists x1; split; auto. intros; intro. appoA2H H17.
    apply Property_Fun in H12; subst; auto. eapply H10; eauto.
    New H16. apply H5 in H16. apply Property_dm in H16; auto.
    New H16. apply Property_Value' in H12; auto.
    appA2G. exists y0. appA2G. split; auto. appoA2G.
Qed.

Lemma lem167b : ∀ {f r}, ω ⊂ ran(f) -> WellOrdered r⁻¹ dom(f)
  -> Order_Pr f r E -> False.
Proof.
  intros. destruct H0.
  set (S := \{ λ u, ∃ w, w ∈ ω /\ [u, w] ∈ f \}).
  assert (S ⊂ dom(f)).
  { red; intros. appA2H H3. rdeHex. eapply Property_dom; eauto. }
  assert (S ≠ Φ).
  { New MKT135a. New H4. apply H in H4. appA2H H4.
    destruct H6. apply NEexE. exists x. appA2G; ope. } 
  destruct (H2 _ H3 H4) as [z []]. appA2H H5.
  destruct H7 as [w []]. apply MKT134 in H7. New H7.
  apply H in H9. appA2H H9. destruct H10.
  assert (x ∈ S). { appA2G; ope. }
  destruct (H6 x); auto. appoA2G. apply MKT96 in H1 as [_ []].
  apply invp1 in H8; apply invp1 in H10.
  assert (w ∈ dom(f⁻¹)). { eapply Property_dom; eauto. }
  assert ((PlusOne w) ∈ dom(f⁻¹)). { eapply Property_dom; eauto. }
  assert (Rrelation w E (PlusOne w)). { appoA2G. appA2G. }
  apply Property_Fun in H8; apply Property_Fun in H10; auto.
  apply H12 in H15; subst; auto.
Qed.

Theorem MKT167 : ∀ x, Finite x <-> ∃ r, WellOrdered r x /\ WellOrdered (r⁻¹) x.
Proof.
  split; intros.
  - New H. appA2H H. destruct H1. apply MKT107 in H1.
    apply Property_Finite,MKT153,MKT146 in H0.
    destruct H0 as [f [? []]].
    exists (\{\ λ u v, Rrelation f[u] E f[v] \}\); split.
    + apply lem167a; auto.
    + assert ((\{\ λ u v, Rrelation f[u] E f[v] \}\)⁻¹
        = \{\ λ u v, Rrelation f[u] E⁻¹ f[v] \}\).
      { eqext; PP H5 a b; appoA2G; appoA2H H7.
        - appA2G. red in H6. rxo; ope.
        - appoA2G. rxo; ope. }
      rewrite H5. apply lem167a; auto.
  - destruct H as [r []]. New (MKT107 MKT113a).
    destruct (MKT99 H H1) as [f]. deand. destruct H3. deand.
    destruct H4; subst.
    + apply MKT114 in H8. New MKT165.
      appA2H H4. destruct H9. appA2H H9.
      destruct (Th110ano H8 H11). deor.
      * apply MKT96 in H6 as [[_ ?]]. rewrite reqdi in H12.
        assert (Ensemble f⁻¹). { apply MKT75; eauto. }
        assert (P[dom(f⁻¹)] = dom(f⁻¹)).
        { apply MKT156. apply MKT164; auto. }
        rewrite <-H15 in H12. rewrite deqri. red.
        destruct (MKT160 H6 H14);
        [eapply H11; eauto|rewrite H16; auto].
      * destruct (lem167b H12 H0 H6).
    + assert (ω ⊂ ran(f)).
      { rewrite H4. red; intros. appA2H H9. destruct H10. appA2G. }
      assert (WellOrdered r⁻¹ dom(f)). 
      { destruct H7. eapply wosub; eauto. }
      destruct (lem167b H9 H10 H6).
Qed.

(* Theo168 if x and y are finite, then x∪y is finite *)
Lemma lem168 : ∀ {x y r s}, WellOrdered r x -> WellOrdered s y
  -> WellOrdered \{\ λ u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v)
    \/ (u ∈ (y ~ x) /\ v ∈ (y ~ x) /\ Rrelation u s v)
    \/ (u ∈ x /\ v ∈ (y ~ x)) \}\ (x ∪ y).
Proof.
  intros. repeat split; try red; intros.
  - destruct H. deHun.
    + New (H _ _ H1 H2); deor; auto; [left|right; left]; appoA2G.
    + TF (u ∈ x).
      * New (H _ _ H4 H2); deor; auto; [left|right; left]; appoA2G.
      * right; left. appoA2G; rxo.
    + TF (v ∈ x).
      * New (H _ _ H1 H4); deor; auto; [left|right; left]; appoA2G.
      * left. appoA2G; rxo.
    + destruct H0. TF (u ∈ x); TF (v ∈ x).
      * New (H _ _ H5 H6); deor; auto; [left|right; left]; appoA2G.
      * left. appoA2G; rxo.
      * right; left. appoA2G; rxo.
      * New (H0 _ _ H1 H2); deor; auto.
        -- left; appoA2G. right; left; auto.
        -- right; left; appoA2G. right; left; auto.
  - TF (\{ λ z, z ∈ y0 /\ z ∈ x \} = Φ).
    + assert (y0 ⊂ y).
      { red; intros. New H4. apply H1 in H4. deHun; auto.
        feine z. rewrite <-H3. appA2G. }
      apply H0 in H4 as [z []]; auto. exists z. split; auto.
      red; intros. appoA2H H7. deor; deand.
      * feine z. rewrite <-H3. appA2G.
      * apply (H5 y1); auto.
      * feine y1. rewrite <-H3. appA2G.
    + assert (\{ λ z, z ∈ y0 /\ z ∈ x \} ⊂ x).
      { red; intros. appA2H H4. tauto. }
      apply H in H4 as [z []]; auto. appA2H H4. destruct H6.
      exists z. split; auto. red; intros. appoA2H H9. deor; deand. 
      * apply (H5 y1); auto. appA2G.
      * apply setminp in H11 as []. auto.
      * apply setminp in H11 as []. auto.
Qed.

Theorem MKT168 : ∀ x y, Finite x -> Finite y -> Finite (x ∪ y).
Proof.
  intros. apply MKT167 in H as [r []].
  apply MKT167 in H0 as [s []]. apply MKT167.
  exists (\{\ λ u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v)
    \/ (u ∈ (y ~ x) /\ v ∈ (y ~ x) /\ Rrelation u s v)
    \/ (u ∈ x /\ v ∈ (y ~ x)) \}\). split.
  - apply lem168; auto.
  - split; try red; intros.
    + destruct (lem168 H H0). New (H5 _ _ H3 H4). deor; auto.
      * right; left. appoA2G; rxo.
      * left. appoA2G; rxo.
    + TF (\{ λ z, z ∈ y0 /\ z ∈ (y ~ x) \} = Φ).
      * destruct (lem168 H1 H2) as [_ ?],(H6 _ H3 H4) as [z []].
        exists z. split; auto. red; intros. appoA2H H10.
        appoA2H H11. deor; deand.
        -- elim (H8 _ H9). apply invp1 in H14. appoA2G.
        -- elim (H8 _ H9). apply invp1 in H14. appoA2G.
        -- feine y1. rewrite <-H5. appA2G.
      * assert (\{ λ z, z ∈ y0 /\ z ∈ (y ~ x) \} ⊂ y).
        { red; intros. appA2H H6. destruct H7. appA2H H8. tauto. }
        apply H2 in H6 as [z []]; auto. appA2H H6. destruct H8.
        exists z. split; auto. red; intros.
        appoA2H H11. appoA2H H12. deor; deand. 
        -- apply setminp in H9 as []. auto.
        -- apply (H7 y1); appA2G.
        -- apply setminp in H9 as []. auto.
Qed.

(* Theo169 if x is finite and each its member is finite, then ∪x is finite *)
Lemma Lemma169 : ∀ x y, ∪(x ∪ y) = (∪x) ∪ (∪y).
Proof.
  intros. eqext; appA2H H.
  - rdeHex. appA2G. deHun; [left|right]; appA2G.
  - destruct H0; appA2H H0; rdeHex; appA2G;
    exists x0; split; try appA2G; auto.
Qed.

Theorem MKT169 : ∀ x, Finite x -> (∀ z, z ∈ x -> Finite z)
  -> Finite (∪ x).
Proof.
  intros. assert (\{ λ u, u∈ω /\ ∀ y, P[y] = u
    -> (∀ z, z ∈ y -> Finite z) -> Finite (∪y) \} = ω).
  { clear H H0. apply MKT137; try red; intros.
    - appA2H H. tauto.
    - appA2G; split; auto. intros. New (carE H).
      subst. red. rewrite MKT24',H; auto.
    - appA2H H. deand. New (MKT134 H0). appA2G. split; auto. intros.
      New H3. apply pveqv in H3; eauto. destruct H3 as [f [[][]]].
      assert (f⁻¹[u] ∈ y).
      { rewrite <-H7,deqri. apply Property_dm; auto.
        rewrite <-reqdi,H8. appA2G. }
        rewrite (Lemma163b H9),Lemma169. apply MKT168.
      + apply H1; intros.
        * apply (finse f); auto.
        * apply H4. appA2H H10. tauto.
      + destruct (@ MKT44 f⁻¹[u]); eauto. rewrite H11. auto. }
  red in H. rewrite <-H1 in H. appA2H H.
  destruct H2. apply H3; auto.
Qed.

(* Theo170 if x and y are finite, then x×y is finite *)
Theorem MKT170 : ∀ x y, Finite x -> Finite y -> Finite (x × y).
Proof.
  intros. TF (y = Φ).
  { assert ((x × Φ) = Φ).
    { eqext; try emf. PP H2 a b. destruct H4. emf. }
    subst; rewrite H2; auto. }
  rewrite <-Lemma74; try apply Property_Finite; auto.
  apply MKT169; intros.
  - assert (x ≈ \{λ z, ∃ u, u ∈ x /\ z = [u] × y \}).
    { exists (\{\ λ u v, u ∈ x /\ v = [u] × y \}\).
      repeat split; auto; try red; try eqext; intros.
      - appoA2H H2. appoA2H H3. destruct H4,H5; subst; auto.
      - PP H2 a b; eauto.
      - appoA2H H2. appoA2H H3. appoA2H H4. appoA2H H5.
        destruct H6,H7; subst; auto. NEele H1.
        assert ([y0,x0] ∈ ([y0] × y)). { appoA2G. rxo. }
        rewrite H9 in H8. appoA2H H8. destruct H10. eins H10.
      - appA2H H2. destruct H3. appoA2H H3. tauto.
      - appA2G. exists [z] × y. appoA2G. rxo.
        apply MKT74; eauto. apply Property_Finite; auto.
      - appA2H H2. destruct H3.
        appoA2H H3. destruct H4. subst. appA2G.
      - appA2H H2. destruct H3,H3. subst.
        appA2G. exists x0. appA2G. }
    New (Property_Finite H). New (eqvp H3 (MKT146 H2)).
    unfold Finite in *. apply MKT154 in H2; auto.
    rewrite <-H2; auto.
  - appA2H H2. destruct H3 as [w []]; subst.
    assert (y ≈ [w] × y).
    { exists (\{\ λ u v, u ∈ y /\ v = [w,u] \}\).
      repeat split; auto; try red; try eqext; intros.
      - appoA2H H4. appoA2H H5. destruct H6,H7; subst; auto.
      - PP H4 a b; eauto.
      - appoA2H H4. appoA2H H5. appoA2H H6. appoA2H H7.
        destruct H8,H9. subst. apply MKT55 in H11 as []; eauto.
      - appA2H H4. destruct H5. appoA2H H5. tauto.
      - appA2G. exists [w,z]. appoA2G. rxo.
      - appA2H H4. destruct H5. appoA2H H5.
        destruct H6. subst. appoA2G.
      - PP H4 a b. destruct H6. eins H5.
        appA2G. exists b. appoA2G. }
    New (Property_Finite H0). New (eqvp H5 (MKT146 H4)).
    unfold Finite in *. apply MKT154 in H4; auto.
    rewrite <-H4; auto.
Qed.

(* Theo171 if x is finite, then pow(x) is finite *)
Lemma lem171 : ∀ {x y}, y ∈ x
  -> pow(x) = pow(x ~ [y]) ∪ \{ λ z, z ⊂ x /\ y ∈ z \}.
Proof.
  intros; eqext; appA2H H0.
  - appA2G. TF (y ∈ z).
    + right. appA2G.
    + left. appA2G. red; intros.
      apply setminP; auto. intro. eins H4.
  - destruct H1; appA2H H1; appA2G. tauto.
Qed.

Theorem MKT171 : ∀ x, Finite x -> Finite pow(x).
Proof.
  intros. assert (\{ λ u, u ∈ ω /\ ∀ y, P[y] = u
    -> Finite pow(y) \} = ω).
  { clear H. apply MKT137; try red; intros.
    - appA2H H. tauto.
    - appA2G; split; auto. intros. New (carE H). subst.
      rewrite powEm. apply finsin; auto.
    - appA2H H. deand. New (MKT134 H0). appA2G. split; auto.
      intros. New H3. rename H4 into G.
      apply pveqv in H3 as [f [[][]]]; eauto.
      assert (f⁻¹[u] ∈ y).
      { rewrite <-H5,deqri. apply Property_dm; auto.
        rewrite <-reqdi,H6. appA2G. } rewrite (lem171 H7).
      assert (Finite pow(y ~ [f⁻¹[u]])).
      { red. apply H1, (finse f); auto. } apply MKT168; auto.
      assert (pow(y ~ [f⁻¹[u]]) ≈ \{ λ z, z ⊂ y /\ f⁻¹[u] ∈ z \}).
      { exists \{\ λ v w, v ∈ pow(y ~ [f⁻¹[u]])
          /\ w = v ∪ [f⁻¹[u]] \}\.
        repeat split; auto; try red; try eqext; intros.
        - appoA2H H9. appoA2H H10. deand; subst; auto.
        - PP H9 a b; eauto.
        - appoA2H H9. appoA2H H10. appoA2H H11. appoA2H H12.
          deand; subst; auto. appA2H H13. appA2H H14. eqext.
          + assert (z0 ∈ (z ∪ [f⁻¹[u]])).
            { rewrite <-H15. appA2G. }
            apply H13 in H17. apply setminp in H17 as [].
            deHun; tauto.
          + assert (z0 ∈ (y0 ∪ [f⁻¹[u]])). { rewrite H15. appA2G. }
            apply H16 in H17. apply setminp in H17 as [].
            deHun; tauto.
        - appA2H H9. destruct H10. appoA2H H10. tauto.
        - appA2G. exists (z ∪ [f⁻¹[u]]). appoA2G. rxo.
          apply AxiomIV; eauto.
        - appA2H H9. destruct H10. appoA2H H10.
          destruct H11. subst. appA2H H11.
          appA2G; split; try red; intros; [deHun|appA2G].
          + apply H11 in H12. appA2H H12. tauto.
          + eins H12.
        - appA2H H9. deand. subst. appA2G. exists (z ~ [f⁻¹[u]]).
          assert (Ensemble (z ~ [f⁻¹[u]])). { eapply MKT33; eauto. }
          appoA2G; split; [|apply Lemma163b; auto]. appA2G.
          red; intros. apply setminp in H12 as [].
          apply setminP; auto. }
      New (Property_Finite H8).
      assert (Ensemble \{λ z, z ⊂ y /\ f⁻¹[u] ∈ z \}).
      { apply MKT146 in H9. eapply eqvp; eauto. }
      apply MKT154 in H9; auto. red. rewrite <-H9; auto. }
  red in H. rewrite <-H0 in H. appA2H H.
  destruct H1. apply H2; auto.
Qed.

(* Theo172 if x is finite, y⊂x and P[y]=P[y], then x=y *)
Theorem MKT172 : ∀ x y, Finite x -> y ⊂ x -> P[y] = P[x] -> x = y.
Proof.
  intros. Absurd. assert (x <> Φ).
  { intro. subst. apply H2. apply MKT27; split; auto. }
  assert (∃ z, z ∈ x /\ ~ z ∈ y).
  { Absurd. elim H2. apply MKT27; split; auto.
    red; intros. Absurd. elim H4; eauto. }
  destruct H4 as [z []]. assert (Ensemble z) by eauto.
  New (finsub H H0). New (finue H7 H6 H5). red in H7.
  assert ((y ∪ [z]) ⊂ x).
  { red; intros. deHun; auto. eins H9. }
  apply MKT158 in H9. rewrite H8,<-H1 in H9.
  assert (P[y] ≺ (PlusOne P[y])). { appA2G. } destruct H9.
  - destruct (MKT102 _ _ H9 H10).
  - rewrite H9 in H10. destruct (MKT101 _ H10).
Qed.

(* Theo173  a property of infinite set *)
Theorem MKT173 : ∀ x, Ensemble x -> ~ Finite x
  -> ∃ y, y ⊂ x /\ y <> x /\ x ≈ y.
Proof.
  intros. apply MKT19 in H. rewrite <-MKT152b in H.
  apply Property_Value in H; auto. appoA2H H. destruct H1.
  assert (ω ⊂ P[x]).
  { appA2H H2. destruct H3. appA2H H3. New MKT138.
    appA2H H6. destruct (Th110ano H5 H7); auto. elim H0; auto. }
  New H1. apply MKT146 in H1 as [f [[] []]].
  assert (x ~ [f[Φ]] <> x).
  { intro. assert (f[Φ] ∈ x).
    { subst. apply Property_dm; auto. rewrite H6. auto. }
    rewrite <-H8 in H9. apply setminp in H9 as []. eauto. }
  assert (K1 : ∀ x, x ∈ ω -> x ∈ dom(f)).
  { intros. subst. rewrite H6; auto. }
  assert (K2 : ∀ x, x ∈ ω -> f[x] ∈ ran(f)).
  { intros. apply Property_dm; auto. }
  exists (x ~ [f[Φ]]). deandG; eauto. eapply MKT147; eauto.
  exists \{\ λ u v, u ∈ P[x] /\ ((u ∈ ω -> v = f[PlusOne u])
    /\ ( ~ u ∈ ω -> v = f[u])) \}\. rewrite <-H6.
  repeat split; auto; try red; try eqext; intros.
  - appoA2H H9. appoA2H H10. deand. TF (x0 ∈ ω).
    + rewrite H13, H15; auto.
    + rewrite H14, H16; auto.
  - PP H9 a b; eauto.
  - appoA2H H9. appoA2H H10. appoA2H H11. appoA2H H12. deand.
    TF (y ∈ ω); TF (z ∈ ω).
    + apply H17 in H19 as ?. apply H15 in H20 as ?. subst.
      apply f11inj in H22; auto. apply MKT136; auto.
    + apply H17 in H19 as ?. rewrite H16 in H21; auto.
      apply f11inj in H21; auto. subst. elim H20; auto.
    + apply H15 in H20 as ?. rewrite H18 in H21; auto.
      apply f11inj in H21; auto. subst. elim H19; auto.
    + apply H16 in H20 as ?. rewrite H18 in H21; auto.
      apply f11inj in H21; subst; auto.
  - appA2H H9. destruct H10. appoA2H H10. tauto.
  - appA2G. TF (z ∈ ω).
    + exists f[PlusOne z]. appoA2G; rxo.
      deandG; auto. intros. tauto.
    + New H9. apply Property_dm in H9; auto.
      exists f[z]. appoA2G; rxo. deandG; auto. intro. tauto.
  - appA2H H9. destruct H10. appoA2H H10. deand. TF (x0 ∈ ω).
    + rewrite H12; auto. apply setminP; subst; auto. intro.
      eins H7. apply f11inj in H7; auto. eapply MKT135b; eauto.
    + rewrite H13; auto. subst. New H11.
      apply Property_dm in H11; auto. apply setminP; auto. intro.
      eins H15. apply f11inj in H15; subst; auto.
  - apply setminp in H9 as []. appA2G. subst. einr H9. TF (x ∈ ω).
    + destruct (caseint H11) as [?|[n []]];
      subst; [elim H10; eauto|].
      exists n. appoA2G; rxo. deandG; auto. intro. tauto.
    + exists x. appoA2G; rxo. deandG; auto. intro. tauto.
Qed.

Theorem MKT174 : ∀ x, x ∈ (R ~ ω) -> P[PlusOne x] = P[x].
Proof.
  intros. apply setminp in H as [].
  assert (x ⊂ (PlusOne x)). { red; intros. appA2G. }
  assert (~ Finite x).
  { intro; apply H0. assert (x ∈ C).
    { appA2G. split; auto. intros. intro. apply MKT154 in H5; eauto.
      appA2H H. apply H6 in H4 as ?. apply MKT172 in H7; auto.
      subst. destruct (MKT101 _ H4). }
    apply MKT156 in H3 as []. rewrite <-H4; auto. }
  apply MKT173 in H2 as [y]; eauto. deand.
  assert (∃ z, z ∈ x /\ ~ z ∈ y).
  { Absurd. elim H3. apply MKT27; split; auto.
    red; intros. Absurd. elim H5. eauto. }
  destruct H5 as [z []], H4 as [f [? []]].
  assert (PlusOne x ≈ y ∪ [z]).
  { exists (f ∪ [[x,z]]). subst. deandG.
    - apply f11pb; eauto. apply MKT101.
    - rewrite undom,domor; eauto.
    - rewrite unran,ranor; eauto. }
  assert ((y ∪ [z]) ⊂ x). { red; intros. deHun; auto. eins H10. }
  apply MKT158 in H10. apply MKT158 in H1.
  apply MKT33 in H2 as ?; eauto. apply MKT154 in H9; eauto;
  [|apply AxiomIV; eauto]. rewrite <-H9 in H10.
  destruct H1,H10; auto. destruct (MKT102 _ _ H1 H10).
Qed.

Lemma lem177a : ∀ {a b}, a ∈ R -> b ∈ R
  -> Max a b = a \/ Max a b = b.
Proof.
  intros. appA2H H. appA2H H0. destruct (MKT109 H1 H2); unfold Max;
  apply MKT29 in H3; [|rewrite MKT6 in H3]; auto.
Qed.

Lemma lem177b : ∀ {a b}, a ∈ R -> b ∈ R -> Max a b ∈ R.
Proof.
  intros. destruct (lem177a H H0); rewrite H1; auto.
Qed.

Lemma lem177c : ∀ P a b c d, Ensemble ([a,b]) -> Ensemble ([c,d])
  -> Rrelation ([a,b]) \{\ λ a b, ∃ u v x y, a = [u,v]
    /\ b = [x,y] /\ P u v x y \}\ ([c,d]) <-> P a b c d.
Proof.
  split; intros.
  - appoA2H H1. destruct H2,H2,H2,H2,H2,H3.
    apply MKT55 in H2 as []; apply MKT55 in H3 as []; ope.
    subst; auto.
  - appA2G. exists [a,b],[c,d]; split; auto. exists a,b,c,d; auto.
Qed.

Theorem MKT177 : WellOrdered ≪ (R × R).
Proof.
  assert (K1 : ∀ j k l, j ∈ l -> k ∈ l -> [j,k] ∈ (l × l)).
  { intros. appA2G; rxo. }
  split; try red; intros.
  - PP H a b. PP H0 c d. deand. New (lem177b H1 H3). appA2H H5.
    New (lem177b H2 H4). appA2H H7. New (MKT110 H6 H8). deor.
    + right. left. apply lem177c; auto.
    + left. apply lem177c; auto.
    + New H1. New H2. appA2H H1. appA2H H2. 
      New (MKT110 H12 H13). deor; subst.
      * right. left. apply lem177c; auto 6.
      * left. apply lem177c; auto 6.
      * New H3. New H4. appA2H H3. appA2H H4.
        New (MKT110 H16 H17). deor; subst; auto.
        { right. left. apply lem177c; auto 7. }
        { left. apply lem177c; auto 7. }
  - NEele H0. New H0. apply H in H1. PP H1 a b. destruct H3.
    set (s1 := \{ λ z, ∃ a b, [a,b] ∈ y /\ z = Max a b \}).
    assert (s1 ⊂ R).
    { red; intros. appA2H H4. rdeHex. subst.
      apply H in H5. appoA2H H5. apply lem177b; tauto. }
    assert (s1 <> Φ).
    { apply NEexE. destruct (lem177a H2 H3);
      [exists a|exists b]; appA2G. }
    apply (MKT107 MKT113a) in H4 as [u []]; auto.
    appA2H H4. destruct H7 as [? [? []]]. subst.
    set (s2 := \{ λ a, ∃ b, [a,b] ∈ y /\ Max a b = Max x x0 \}).
    assert (s2 ⊂ R).
    { red; intros. appA2H H8. rdeHex.
      apply H in H9. appoA2H H9. tauto. }
    assert (s2 <> Φ).
    { New H7. apply H in H7. appoA2H H7. destruct H10.
      apply NEexE. exists x; appA2G. }
    apply (MKT107 MKT113a) in H9 as [u []]; auto. appA2H H9. rdeHex.
    set (s3 := \{ λ b, ∃ a, [a,b] ∈ y /\ Max a b = Max x x0
      /\ a = u \}).
    assert (s3 ⊂ R).
    { red; intros. appA2H H13. rdeHex.
      apply H in H14. appoA2H H14. tauto. }
    assert (s3 <> Φ).
    { New H7. apply H in H7. appoA2H H7. destruct H15. apply NEexE.
      exists x1; appA2G. ope. }
    apply (MKT107 MKT113a) in H14 as [v []]; auto. appA2H H14.
    rdeHex. subst. exists ([u,v]); split; auto.
    unfold not; intros. New H18.  apply H in H18. PP H18 p q.
    apply lem177c in H19; rxo. deand; deor; deand.
    + apply (H6 (Max p q)); [appA2G|appoA2G]. rewrite <-H17; auto.
    + apply (H10 p); [appA2G|appoA2G]; ope.
      rewrite <-H17,<-H23; eauto.
    + apply (H15 q); [appA2G|appoA2G].
      rewrite <-H17,<-H23; eauto.
Qed.

Lemma lem178a : ∀ {a b}, a ∈ R -> b ∈ R
  -> a ∈ (PlusOne (Max a b)).
Proof.
  intros. destruct (lem177a H H0); rewrite H1; appA2G.
  apply MKT29 in H1. appA2H H. appA2H H0.
  destruct (Th110ano H2 H3); auto. right.
  apply MKT41; eauto. apply MKT27; auto.
Qed.

Lemma lem178b : ∀ u v x y, u ∈ R -> v ∈ R -> x ∈ R -> y ∈ R
  -> Max u v ≺ Max x y \/ Max u v = Max x y
  -> PlusOne (Max u v) ⊂ PlusOne (Max x y).
Proof.
  unfold Included; intros. New (lem177b H H0).
  New (lem177b H1 H2). appA2H H5. appA2H H6.
  destruct H3; try rewrite <-H3; eincus H4; try appA2G.
  left. eapply H8; eauto.
Qed.

Theorem MKT178 : ∀ u v x y, Rrelation ([u,v]) ≪ ([x,y])
  -> [u,v] ∈ ((PlusOne (Max x y)) × (PlusOne (Max x y))).
Proof.
  intros. red in H. New H. apply lem177c in H; ope. deand.
  appoA2H H. appoA2H H1. deand. New (lem178a H6 H3).
  rewrite MKT6 in H7. New (lem178a H3 H6).
  deor; deand; appoA2G; split; apply (lem178b u v); auto.
Qed.

Fact le179 : ∀ x, x ∈ R -> P[x] ∈ ω -> P[x] = x.
Proof.
  intros. apply MKT156. appA2G. split; auto. intros.
  intro. apply MKT154 in H3; eauto. appA2H H. New H2.
  apply H4 in H2. apply MKT172 in H2; auto. subst.
  eapply MKT101; eauto.
Qed.

Fact t69r : ∀ f x, Function f -> Ensemble f[x] -> f[x] ∈ ran(f).
Proof.
  intros. apply MKT19, MKT69b' in H0. apply Property_dm; auto.
Qed.

Fact CsubR : C ⊂ R.
Proof.
  red; intros. appA2H H. destruct H0. auto.
Qed.

Global Hint Resolve CsubR : core.

Fact plusoneEns : ∀ z, Ensemble z -> Ensemble (PlusOne z).
Proof. 
  intros. apply AxiomIV; auto.
Qed.

Global Hint Resolve plusoneEns : core.

Fact pclec : ∀ {x}, x ∈ R -> P[x] ≼ x.
Proof.
  intros. appA2H H. New H. apply Property_PClass in H. appA2H H.
  destruct H2. appA2H H2. red. New (MKT110 H4 H0). deor; auto.
  apply H3 in H5; [|appA2G]. elim H5. apply MKT153; auto.
Qed.

Lemma lem179a : ∀ x y, Ensemble x -> Ensemble y
  -> P[x×y] = P[(P[x]) × (P[y])].
Proof.
  intros. New H. New H0. apply MKT153,MKT146 in H1 as [f].
  apply MKT153,MKT146 in H2 as [g]. deand.
  New (Property_PClass H). New (Property_PClass H0).
  apply MKT154; try apply MKT74; eauto.
  exists \{\ λ u v, ∃ a b, u=[a,b] /\ v = [f[a],g[b]] \}\.
  repeat split; auto; try red; intros.
  - appoA2H H9. appoA2H H10. destruct H11,H11,H12,H12.
    deand. subst. apply MKT49b in H9 as [].
    apply MKT55 in H12 as []; subst; ope; auto.
  - PP H9 a b; eauto.
  - appoA2H H9. appoA2H H10. appoA2H H11. appoA2H H12.
    destruct H13,H13,H14,H14. deand. subst.
    apply MKT49b in H9 as []. New H3. rewrite H15 in H9.
    apply MKT55 in H15 as []; ope. destruct H1,H2.
    apply f11inj in H13; apply f11inj in H14; subst; auto;
    apply MKT69b'; apply MKT19; ope.
  - eqext.
    + appA2H H9. destruct H10. appoA2H H10. destruct H11,H11,H11.
      subst. appoA2G. apply MKT49b in H10 as [].
      split; apply MKT69b'; apply MKT19; ope.
    + PP H9 a b. deand. appA2G. exists ([f[a],g[b]]). appoA2G.
      rxo; apply MKT19; apply MKT69b; auto.
  - destruct H1, H2. eqext.
    + appA2H H11. destruct H12. appoA2H H12. destruct H13,H13,H13.
      subst. appoA2G. apply MKT49b in H12 as []. rewrite <-H4,<-H6.
      split; apply t69r; ope; auto.
    + PP H11 a b. deand. appA2G. rewrite <-H4,<-H6 in *.
      einr H3. einr H5. exists [x,x0]. appoA2G. rxo.
Qed.

Lemma lem179b : ∀ z x, x ∈ C -> z ∈ R -> P[z] ∈ x -> z ∈ x.
Proof.
  intros. New H. appA2H H. apply Property_PClass in H. appA2H H.
  destruct H3. appA2H H3. apply MKT156 in H2 as []. appA2H H0.
  rewrite <-H7 in H1.  New (MKT110 H8 H6). deor; auto.
  - apply H8,MKT158 in H9. destruct H9.
    + destruct (MKT102 _ _ H1 H9). 
    + rewrite H9 in H1. destruct (MKT101 _ H1).
  - subst. destruct (MKT101 _ H1).
Qed.

Theorem MKT179 : ∀ {x}, x ∈ (C ~ ω) -> P[x × x] = x.
Proof.
  intros. Absurd.
  assert (\{ λ x, x ∈ (C ~ ω) /\ P[x × x] <> x \} <> Φ).
  { apply NEexE. exists x. appA2G. }
  assert (\{ λ x, x ∈ (C ~ ω) /\ P[x × x] <> x \} ⊂ C).
  { red; intros. appA2H H2. destruct H3. appA2H H3. tauto. }
  apply MKT150 in H2 as [z []]; auto. appA2H H2. deand.
  assert (Ensemble z×z). { apply MKT74; eauto. }
  apply setminp in H4 as [].
  assert (WellOrdered ≪ z × z).
  { apply (wosub R×R); [apply MKT177|]. red; intros. PP H8 a b.
    destruct H10. appA2H H4. destruct H11. appA2H H11.
    appoA2G; split; appA2G; eapply MKT111; eauto. }
  destruct (MKT100 H8 (MKT107 MKT113a)) as [f]; auto. deand.
  rewrite <-H11 in H6. elim H5. New H4. apply MKT156 in H4 as [].
  pattern z at 3. rewrite <-H13. red in H10. deand.
  assert (Ensemble ran(f)). { apply AxiomV; auto. }
  apply MKT27; split.
  - assert (ran(f) ⊂ z).
    { red; intros. einr H19. New H19.
      rewrite H11 in H19. PP H19 u v. deand.
      apply MKT96 in H15 as ?. destruct H24 as [[_]].
      set (d := \{\ λ a b, Rrelation ([a,b]) ≪ ([u,v])
        /\ [a,b] ∈ dom(f) \}\).
      assert (d ≈ f[[u,v]]).
      { assert (Function (f|(d))). { apply MKT126a; auto. }
        assert (dom(f|(d)) = d). { rewrite MKT126b; auto.
        apply MKT30. red; intros. PP H27 a b. tauto. }
        exists (f|(d)). deandG; [split|..]; auto.
        - split; try red; intros; [PP H28 a b; eauto|].
          appoA2H H28. appoA2H H29. appA2H H30. appA2H H31.
          deand. eapply H24; apply invp1; eauto.
        - eqext.
          + einr H28. rewrite MKT126c in *; auto.
            rewrite H27 in H28. PP H28 a b. deand.
            apply H15 in H30; auto. appoA2H H30; auto.
          + apply MKT114 in H17. apply H17 in H28 as ?; auto.
            einr H29. New H29. rewrite H11 in H29. PP H29 a b.
            deand. apply Property_Value' in H30 as ?; auto. appA2G.
            exists [a,b]. appA2G. split; auto. appoA2G.
            split; eauto. appoA2G. split; auto.
            rewrite reqdi in H20,H30. eapply H25 in H20; eauto.
            * rewrite f11iv,f11iv in H20; auto.
            * appoA2G. rxo. }
      assert (d ⊂ (PlusOne (Max u v)) × ((PlusOne (Max u v)))).
      { red; intros. PP H27 a b. apply MKT178; tauto. }
      assert ((Max u v) ∈ z).
      { appA2H H12. destruct H28. appA2H H28.
        apply MKT111 in H22 as ?; apply MKT111 in H23 as ?; auto.
        assert (u ∈ R) by appA2G. assert (v ∈ R) by appA2G.
        destruct (lem177a H33 H34); rewrite H35; auto. }
      assert (P[Max u v] ∈ z) as G1.
      { apply CsubR in H12. appA2H H12. New H29.
        eapply MKT111 in H29; eauto.
        assert ((Max u v) ∈ R) by appA2G.
        destruct (pclec H31); [eapply H30|rewrite H32]; eauto. }
      apply MKT33 in H27 as ?; [|apply MKT74; apply AxiomIV; eauto].
      apply MKT154 in H26; eauto. apply MKT158 in H27.
      rewrite H26 in H27. TF (P[Max u v] ∈ ω).
      - assert (Finite (PlusOne (Max u v))).
        { red; unfold PlusOne; rewrite finue; eauto. apply MKT101. }
        eapply MKT170 in H31; eauto. red in H31.
        assert (P[f[[u,v]]] ∈ ω).
        { destruct H27; [|rewrite H27; auto].
          New MKT138. appA2H H32. eapply H33; eauto. }
        apply H17 in H20. rewrite <-(le179 f[[u,v]]); auto.
        New MKT138. appA2H H33. apply Property114 in H34.
        appA2H H12. destruct H35.
        eapply Lemma99c in H34; eauto. appoA2H H34; auto.
      - assert (Ensemble (Max u v)) by eauto.
        apply Property_PClass in H31. appA2H H31. destruct H32.
        assert (P[Max u v] ∈ (R ~ ω)). { apply setminP; auto. } 
        assert (P[(P[(Max u v)]) × (P[(Max u v)])] = P[(Max u v)]).
        { Absurd. destruct (H3 (P[Max u v])).
          - appA2G. split; auto. apply setminP; auto.
            apply Property_PClass; eauto.
          - appoA2G. }
        rewrite lem179a,MKT174,H35 in H27; eauto.
        assert (P[f[[u,v]]] ∈ z).
        { destruct H27; [|rewrite H27; auto].
          apply CsubR in H12. appA2H H12. eapply H36; eauto. }
        eapply lem179b; eauto. apply H17; auto. apply setminP.
        + New (CsubR _ H12). eapply MKT113a; eauto.
        + intro. apply H30. New H36.
          apply MKT164, MKT156 in H36 as []. rewrite H38; auto. }
    assert (dom(f) ≈ ran(f)).
    { apply MKT96 in H15 as []. exists f; auto. }
    apply MKT154 in H20; auto. apply MKT158 in H19.
    rewrite <-H20,H11 in H19. red; intros.
    + destruct H19.
      * assert (Ordinal P[z]).
        { apply Property_PClass,CsubR in H2. appA2H H2. auto. }
        eapply H22; eauto.
      * rewrite <-H19; auto.
  - set (g := \{\ λ u v, u ∈ z /\ v = [u,u] \}\).
    assert (Function g).
    { split; unfold g; auto. intros. appoA2H H19.
      appoA2H H20. deand. subst; auto. }
     assert (Function1_1 \{\ λ u v, u ∈ z /\ v = [u,u] \}\).
    { split; auto. split; try red; intros.
      - PP H20 a b; eauto.
      - appoA2H H20. appoA2H H21. appoA2H H22. appoA2H H23. deand.
        subst; auto. apply MKT55 in H26 as []; subst; eauto. }
    assert (dom(g) = z).
    { eqext.
      + appA2H H21. destruct H22. appoA2H H22. tauto.
      + appA2G. exists [z0,z0]; appoA2G. rxo. }
    assert (ran(g) ⊂ (z × z)).
    { red; intros. appA2H H22. destruct H23. appoA2H H23. deand.
      rewrite H25. appoA2G; rxo. }
    assert (dom(g) ≈ ran(g)). { exists g; auto. }
    apply MKT154 in H23; auto. apply MKT158 in H22.
    rewrite <-H23,H21 in H22. red; intros.
    + destruct H22.
      * assert (Ordinal P[z×z]).
        { New (MKT74 H2 H2). apply Property_PClass,CsubR in H25.
          appA2H H25. auto. } eapply H25; eauto.
      * rewrite <-H22; auto.
    + rewrite H21; auto.
    + New (MKT74 H2 H2). eapply MKT33; eauto.
Qed.

Fact wh1 : ∀ {x y}, Ensemble x -> y <> Φ -> P[y] ⊂ P[x]
  -> P[x] ≼ P[y×x].
Proof.
  intros. NEele H0.
  set (f := \{\ λ u v, u ∈ x /\ v = [x0,u] \}\).
  assert (Function f).
  { split; unfold f; auto. intros. appoA2H H2.
    appoA2H H3. deand. subst; auto. }
    assert (Function1_1 \{\ λ u v, u ∈ x /\ v = [x0,u] \}\).
    { split; auto. split; try red; intros.
      - PP H3 a b; eauto.
      - appoA2H H3. appoA2H H4. appoA2H H5. appoA2H H6. deand.
        subst; auto. apply MKT55 in H9 as []; subst; eauto. }
    assert (dom(f) = x).
    { eqext.
      + appA2H H4. destruct H5. appoA2H H5. tauto.
      + appA2G. exists [x0,z]; appoA2G. rxo. }
    assert (ran(f) ⊂ (y × x)).
    { red; intros. appA2H H5. destruct H6. appoA2H H6. deand.
      rewrite H8. appoA2G; rxo. }
    assert (dom(f) ≈ ran(f)). { exists f; auto. }
    apply MKT154 in H6; auto. apply MKT158 in H5.
    rewrite <-H6,H4 in H5. auto.
    - rewrite H4; auto.
    - apply MKT33 in H5; eauto. apply MKT74; auto.
      assert (Ensemble P[y]).
      { apply Property_PClass in H.
        eapply MKT33; try apply H1; eauto. }
      apply MKT19,MKT69b' in H8; eauto.
Qed.

Fact wh2 : ∀ x y, x ⊂ y -> (x × y) ⊂ (y × y).
Proof.
  unfold Included; intros. PP H0 a b. destruct H2. appoA2G.
Qed.

Fact wh3 : ∀ x y, Ensemble x -> Ensemble y -> P[x × y] = P[y × x].
Proof.
  intros. apply MKT154; try apply MKT74; auto.
  exists (\{\ λ u v, u ∈ (x × y)
    /\ v = [(Second u),(First u)] \}\).
  deandG; [split; split; auto|..]; try red; intros.
  - appoA2H H1. appoA2H H2. deand. subst; auto.
  - PP H1 a b. eauto.
  - appoA2H H1. appoA2H H2. appoA2H H3. appoA2H H4. deand. subst.
    PP H5 a b. PP H6 c d. deand.
    do 2 rewrite MKT54a,MKT54b in H7; eauto.
    apply MKT55 in H7 as []; subst; eauto.
  - eqext.
    + appA2H H1. destruct H2. appoA2H H2. tauto.
    + appA2G. exists [(Second z),(First z)]. appoA2G. rxo.
      * PP H1 a b. destruct H3. rewrite MKT54b; eauto.
      * PP H1 a b. destruct H3. rewrite MKT54a; eauto.
  - eqext.
    + appA2H H1. destruct H2. appoA2H H2. destruct H3. subst.
      PP H3 a b. destruct H5. rewrite MKT54a,MKT54b; eauto.
      appoA2G. rxo.
    + appA2G. PP H1 a b. destruct H3. exists [b,a].
      appoA2G; [rxo|split]; [appoA2G; rxo|].
      rewrite MKT54a,MKT54b; eauto.
Qed.

Theorem MKT180a : ∀ x y, x ∈ C -> y ∈ C -> y ∉ ω -> x ≠ Φ
  -> P[x] ⊂ P[y] -> P[x × y] = Max P[x] P[y].
Proof.
  intros. assert (y ∈ (C ~ ω)) by auto. New H4.
  apply MKT179 in H4. assert (Ensemble y) by eauto.
  New (wh1 H6 H2 H3). apply wh2 in H3 as ?. apply MKT158 in H8.
  rewrite <-lem179a,<-lem179a in H8; eauto. New (MKT179 H5).
  unfold Max. apply MKT29 in H3. rewrite H3. rewrite H9 in *.
  apply MKT156 in H0 as []. rewrite H10 in *.
  destruct H7,H8; auto. destruct (MKT102 _ _ H7 H8). 
Qed.

Theorem MKT180b : ∀ x y, x ∈ C -> y ∈ C -> y ∉ ω -> x ≠ Φ -> y ≠ Φ
  -> P[x × y] = Max P[x] P[y].
Proof.
  intros. assert (P[x] ⊂ P[y] \/ P[y] ⊂ P[x]).
  { New H. New H0. apply MKT156 in H as [].
    apply MKT156 in H0 as []. rewrite H6,H7. apply CsubR in H4.
    apply CsubR in H5. appA2H H4. appA2H H5. apply MKT109; auto. }
  destruct H4.
  - apply MKT180a; auto.
  - unfold Max. rewrite wh3,MKT6; eauto. apply MKT180a; auto.
    intro. apply H1. New H. New H0. apply MKT156 in H as [].
    apply MKT156 in H0 as []. rewrite H8,H9 in *.
    appA2H H6. appA2H H7. destruct H10,H11.
    appA2H H10. appA2H H11. apply MKT118 in H4 as []; subst; auto.
    New MKT138. appA2H H16. eapply H17; eauto.
Qed.

Theorem MKT180 : ∀ x y, x ∈ C -> y ∈ C -> x ∉ ω \/ y ∉ ω -> x ≠ Φ
  -> y ≠ Φ -> P[x × y] = Max P[x] P[y].
Proof.
  intros. destruct H1.
  - unfold Max. rewrite wh3,MKT6; eauto. apply MKT180b; auto.
  - apply MKT180b; auto.
Qed.

Fact wh4 : ∀ x y, x ⊂ y -> (y ~ x) ∪ x = y.
Proof.
  intros; eqext.
  - deHun; auto. apply setminp in H0 as []; auto.
  - TF (z ∈ x); deGun; auto.
Qed.

Theorem MKT181a : ∃ f, Order_Pr f E E /\ dom(f) = R
  /\ ran(f) = C ~ ω.
Proof.
  New (MKT107 MKT113a). assert ((C ~ ω) ⊂ R).
  { red; intros. apply setminp in H0 as [].
    appA2H H0; destruct H2. auto. }
  apply wosub with (r := E) in H0; auto.
  destruct (MKT99 H H0) as [f ]. deand. red in H2. deand.
  exists f. destruct H3; deandG; auto; Absurd.
  - eapply MKT91 in H8 as [v []]; eauto.
    assert (Ensemble ran(f)).
    { rewrite H9. eapply (MKT33 v); eauto. red; intros.
      appA2H H10. deand. appoA2H H12. auto. }
    rewrite reqdi in H10. rewrite deqri in H3.
    apply MKT96 in H5 as [[]]. apply AxiomV in H10; auto.
    rewrite H3 in H10. destruct (MKT113b H10).
  - eapply MKT91 in H8 as [v []]; eauto.
    assert (Ensemble dom(f)).
    { rewrite H9. eapply (MKT33 v); eauto. red; intros.
      appA2H H10. deand. appoA2H H12. auto. }
    destruct H5. apply AxiomV in H10; auto. rewrite H3 in H10.
    elim MKT162. rewrite <-(wh4 ω); [|apply MKT164].
    New MKT138. appA2H H12. apply AxiomIV; auto.
Qed.

Theorem MKT181b : ∀ f g, Order_Pr f E E -> Order_Pr g E E
  -> dom(f) = R -> dom(g) = R -> ran(f) = C ~ ω
  -> ran(g) = C ~ ω -> f = g.
Proof.
  intros. inversion H; inversion H0. deand.
  assert (rSection dom(f) E R).
  { rewrite H1. apply Property114,MKT113a. }
  assert (rSection dom(g) E R).
  { rewrite H2. apply Property114,MKT113a. }
  assert (rSection ran(f) E (C ~ ω)).
  { rewrite H3. red. deandG; auto. rewrite <-H3; auto. }
  assert (rSection ran(g) E (C ~ ω)).
  { rewrite H4. red. deandG; auto. rewrite <-H4; auto. }
  apply MKT71; auto; intros. TF (x ∈ dom( f)).
  - destruct (MKT97 H H0 H13 H14 H15 H16);
    [|symmetry; rewrite H1,<-H2 in H17]; apply subval; auto.
  - rewrite (@ MKT69a x); auto. rewrite H1,<-H2 in H17.
    rewrite MKT69a; auto.
Qed.
