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
(*      This file presents the formalization of definitions and axioms        *)
(*                of Morse-Kelley (MK) axiomatic set theory.                  *)
(******************************************************************************)

(** mk_structure *)

(* Pre_Logic *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

Notation "∃! x .. y , P" := (exists ! x, .. (exists ! y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃! x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Axiom classic : ∀ P, P \/ ~P.

Proposition peirce : ∀ P, (~P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Proposition notandor : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition inp : ∀ {P Q: Prop}, (P -> Q) -> (~Q) -> (~P).
Proof.
  intros; intro; auto.
Qed.

(* Structure *)

Parameter Class : Type.
Parameter In : Class -> Class -> Prop.
Parameter Classifier : (Class -> Prop) -> Class.

Notation "x ∈ y" := (In x y) (at level 70).
Notation "\{ P \}" := (Classifier P) (at level 0).

(* Definitions *)

Definition Ensemble x := ∃ y, x ∈ y.

Global Hint Unfold Ensemble : core.

(* Def2 union  x∪y = {z : z∈x or z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* Def3  intersection x∩y = {z : z∈x and z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* Def9  x∉y iff x∈y is not true *)
Definition NotIn x y := ~ (x ∈ y).
Notation "x ∉ y" := (NotIn x y) (at level 70).

(* Def10  ¬x={y：y∉x} *)
Definition Complement x := \{λ y, y ∉ x \}.
Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* Def13  x~y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).
Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* Def85  x≠y iff x=y is not true *)
Notation "x ≠ y" := (~ (x = y)) (at level 70).

(* Def15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* Def18  universe μ={x : x=x} *)
Definition μ := \{ λ x, x = x \}.

(* Def22  ∩x={z : for each y, if y∈x then z∈y} *) 
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.
Notation "∩ x" := (Element_I x) (at level 66).

(* Def23  ∪x={z : for some y, z∈y and y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.
Notation "∪ x" := (Element_U x) (at level 66).

(* Def25  x⊂y iff (for each z, if z∈x then z∈y) *)
Definition Included x y := ∀ z, z ∈ x -> z ∈ y.
Notation "x ⊂ y" := (Included x y) (at level 70).

(* Def36  power class of x = {y : y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.
Notation "pow( x )" := (PowerClass x)(at level 0, right associativity).

(* Def40  [x]={z : if x∈μ then z=x} *)
Definition Singleton x := \{ λ z, x ∈ μ -> z = x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

(* Def45  [x|y]=[x]∪[y] *)
Definition Unordered x y := [x] ∪ [y].
Notation "[ x | y ]" := (Unordered x y) (at level 0).

(* Def48  orderded pairs [x,y] = [[x]|[x|y]] *)
Definition Ordered x y := [ [x] | [x|y]].
Notation "[ x , y ]" := (Ordered x y) (at level 0).

(* Def51  first coordinate of z = ∩∩z *)
Definition First z := ∩∩z.

(* Def52  second coordinate of z = (∩∪z)∪(∪∪z)~(∪∩z) *)
Definition Second z := (∩∪z)∪(∪∪z) ~ (∪∩z).

(* Def56  r is a relation iff for each its member z,
          there exists x and y such that z=[x,y];
          a relation is a class whose members are orderded pairs. *)
Definition Relation r := ∀ z, z ∈ r -> ∃ x y, z = [x,y].

(* { (x,y) : ... } *)
Notation "\{\ P \}\" :=
  (\{ λ z, ∃ x y, z = [x,y] /\ P x y \}) (at level 0).

(* Def57 r∘s is the composition of r and s *)
Definition Composition r s :=
  \{\ λ x z, ∃ y, [x,y] ∈ s /\ [y,z] ∈ r \}\.
Notation "r ∘ s" := (Composition r s) (at level 50).

(* Def60  r ⁻¹={[x,y]:[y,x]∈r} *)
Definition Inverse r := \{\ λ x y, [y,x] ∈ r \}\.
Notation "r ⁻¹" := (Inverse r) (at level 5).

(* Def63 f is a function iff f is a relation and for each x, y, z,
         if [x,y]∈f and [x，z]∈f then y=z *)
Definition Function f  :=
  Relation f /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z).

(* Def65 domain of f = {x : there exists some y, [x,y]∈f} *)
Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.
Notation "dom( f )" := (Domain f)(at level 5).

(* Def66 range of f = {y : there exists some x, [x,y]∈f} *)
Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.
Notation "ran( f )" := (Range f)(at level 5).

(* Def68 value of f at x, f(x) = ∩{y:[x,y]∈f} *)
Definition Value f x := ∩(\{ λ y, [x,y] ∈ f \}).

Notation "f [ x ]" := (Value f x)(at level 5).

(* Def72 Cartesian product x × y = {[u,v] : u∈x /\ v∈y} *)
Definition Cartesian x y := \{\ λ u v, u ∈ x /\ v ∈ y \}\.
Notation "x × y" := (Cartesian x y) (at level 2, right associativity).

(* Def76 Exponent y x = {f : f is a function whose domain is x
                             and range contained in y}            *)
Definition Exponent y x :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

(* Def78 f on x iff f is a function and domain f is x *)
Definition On f x := Function f /\ dom(f) = x.

(* Def79 f to y iff f is a function and range f is contained in y *)
Definition To f y := Function f /\ ran(f) ⊂ y.

(* Def80 f onto y iff f is a function and range f is  y           *)
Definition Onto f y := Function f /\ ran(f) = y.

(* Def81 x is r-related to y; x r-precedes y; xry *)
Definition Rrelation x r y := [x,y] ∈ r.

(* Def82 r connects x; trichotomy                 *)
Definition Connect r x := ∀ u v, u ∈ x -> v ∈ x
  -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u = v).

(* Def83 transitivity, if urv and vrw, then urw *)
Definition Transitive r x := ∀ u v w, u ∈ x -> v ∈ x -> w ∈ x
  -> Rrelation u r v -> Rrelation v r w -> Rrelation u r w.

(* Def84 asymmetry, if urv then vru is not true *)
Definition Asymmetric r x := ∀ u v, u ∈ x -> v ∈ x
  -> Rrelation u r v -> ~ Rrelation v r u.

(* Def86 z is the r-first member of x, iff
         z ∈ x and if y ∈ x then yrz is false *)
Definition FirstMember z r x := z ∈ x /\ (∀ y, y ∈ x -> ~ Rrelation y r z).

(* Def87 r well-orders x iff r connects x and
         if y ⊂ x and y ≠ Φ then there is an r-firstmember of y *)
Definition WellOrdered r x :=
  Connect r x /\ (∀ y, y ⊂ x -> y ≠ Φ -> ∃ z, FirstMember z r y).

(* Def89 y is an r-section of x iff y ⊂ x and r well-orders x and
         for each u ∈ x, v ∈ y, if urv then u ∈ y *)
Definition rSection y r x := y ⊂ x /\ WellOrdered r x
  /\ (∀ u v, u ∈ x -> v ∈ y -> Rrelation u r v -> u ∈ y).

(* Def93 f is r-s order preserving iff f is a function and r well-orders domain f
         and s well-orders range f and f(u)sf(v) whenever urv (u,v ∈ domain f)  *)
Definition Order_Pr f r s := Function f
  /\ WellOrdered r dom(f) /\ WellOrdered s ran(f)
  /\ (∀ u v, u ∈ dom(f) -> v ∈ dom(f) -> Rrelation u r v -> Rrelation f[u] s f[v]).

(* Def95 f is an 1-1 function (bijective function) *)
Definition Function1_1 f := Function f /\ Function (f⁻¹).

(* Def98 f is r-s order preserving in x and y iff r well-orders x,
         s well-orders y, f is r-s order preserving,
         domain f is an r-section of x and range f is an s-section of y   *)
Definition Order_PXY f x y r s := WellOrdered r x /\ WellOrdered s y
  /\ Order_Pr f r s /\ rSection dom(f) r x /\ rSection ran(f) s y.

(* Def103 E-relation, i.e., ∈-relation  *)
Definition E := \{\ λ x y, x ∈ y \}\.

(* Def105 x is full  *)
Definition Full x := ∀ m, m ∈ x -> m ⊂ x.

(* Def106 ordinal *)
Definition Ordinal x := Connect E x /\ Full x.

(* Def112 the class consisting of all ordinals that are sets *)
Definition R := \{ λ x, Ordinal x \}.

(* Def115 ordinal number; this is different from 'ordinal' *)
Definition Ordinal_Number x := x ∈ R.

(* Def116 *)
Definition Less x y := x ∈ y.
Notation "x ≺ y" := (Less x y) (at level 67, left associativity).

(* Def117 *)
Definition LessEqual (x y: Class) := x ∈ y \/ x = y.
Notation "x ≼ y" := (LessEqual x y) (at level 67, left associativity).

(* Def122 successor of x *)
Definition PlusOne x := x ∪ [x].

(* Def125 restriction of f to x *)
Definition Restriction f x := f ∩ (x × μ).
Notation "f | ( x )" := (Restriction f x) (at level 30).

(* Def129 (non-negative) integers; also can be regarded as natural numbers *)
Definition Integer x := Ordinal x /\ WellOrdered (E⁻¹) x.

(* Def130 *)
Definition LastMember x E y := FirstMember x (E⁻¹) y.

(* Def131 natural number set *)
Definition ω := \{ λ x, Integer x \}.

(* Def139 choice function *)
Definition ChoiceFunction c :=
  Function c /\ (∀ x, x ∈ dom(c) -> c[x] ∈ x).

(* Def141 n is a nest : ··· ⊂ x ⊂ y ⊂ z ⊂ ···  *)
Definition Nest n := ∀ x y, x ∈ n -> y ∈ n -> x ⊂ y \/ y ⊂ x.

(* Def144 x≈y iff there exists an 1-1 function between x and y  *)
Definition Equivalent x y :=
  ∃ f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.
Notation "x ≈ y" := (Equivalent x y) (at level 70).

(* Def148 x is a cardinal number, namely, x is an ordinal number and
          if y∈R and y ≺ x, then x≈y is false *)
Definition Cardinal_Number x  :=
  Ordinal_Number x /\ (∀ y, y ∈ R -> y ≺ x -> ~ (x ≈ y)).

(* Def149 C = { x : x is a cardinal number }; C is the class of cardinal numbers *)
Definition C := \{ λ x, Cardinal_Number x \}.

(* Def151 P = { (x,y) : x ≈ y and y ∈ C } cardinality function;
          to map a set to its cardinality *)
Definition P := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

(* Def166 x is finite *)
Definition Finite x := P[x] ∈ ω.

Definition Max x y := x ∪ y.

Definition LessLess := \{\ λ a b, ∃ u v x y, a = [u,v]
  /\ b = [x,y] /\ [u,v] ∈ (R × R) /\ [x,y] ∈ (R × R)
  /\ ((Max u v ≺ Max x y) \/ (Max u v = Max x y /\ u ≺ x)
    \/ (Max u v = Max x y /\ u = x /\ v ≺ y)) \}\.

Notation "≪" := (LessLess)(at level 0, no associativity).

(* Axioms *)

Class MK_Axioms := {
  A_I : ∀ x y, x = y <-> (∀ z, z ∈ x <-> z ∈ y);
  A_II : ∀ b P, b ∈ \{ P \} <-> Ensemble b /\ (P b);
  A_III : ∀ {x}, Ensemble x
    -> ∃ y, Ensemble y /\ (∀ z, z ⊂ x -> z ∈ y);
  A_IV : ∀ {x y}, Ensemble x -> Ensemble y -> Ensemble (x ∪ y);
  A_V : ∀ {f}, Function f -> Ensemble dom(f) -> Ensemble ran(f);
  A_VI : ∀ x, Ensemble x -> Ensemble (∪x);
  A_VII : ∀ x, x ≠ Φ -> ∃ y, y ∈ x /\ x ∩ y = Φ;
  A_VIII : ∃ y, Ensemble y /\ Φ ∈ y
    /\ (∀ x, x ∈ y -> (x ∪ [x]) ∈ y);
  }.

Parameter MK_Axiom : MK_Axioms.

Notation AxiomI := (@ A_I MK_Axiom).
Notation AxiomII := (@ A_II MK_Axiom).
Notation AxiomIII := (@ A_III MK_Axiom).
Notation AxiomIV := (@ A_IV MK_Axiom).
Notation AxiomV := (@ A_V MK_Axiom).
Notation AxiomVI := (@ A_VI MK_Axiom).
Notation AxiomVII := (@ A_VII MK_Axiom).
Notation AxiomVIII := (@ A_VIII MK_Axiom).

Axiom AxiomIX : ∃ c, ChoiceFunction c /\ dom(c) = μ ~ [Φ].

(* tactics *)

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

Ltac deand :=
  match goal with
   | H: ?a /\ ?b |- _ => destruct H; deand
   | _ => idtac
  end.

Ltac deor :=
  match goal with
   | H: ?a \/ ?b |- _ => destruct H; deor
   | _ => idtac 
  end.

Ltac deandG :=
  match goal with
    |- ?a /\ ?b => split; deandG
    | _ => idtac
  end.

Ltac eqext := apply AxiomI; split; intros.

Ltac appA2G := apply AxiomII; split; eauto.

Ltac appA2H H := apply AxiomII in H as [].

