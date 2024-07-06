(**********************************************************************)
(* This is part of MK_Str1, it is distributed under the terms of the  *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2028                            *)
(*    Dakai Guo, Si Chen, Guowei Dou, Shukun Leng and Wensheng Yu     *)
(**********************************************************************)

(** mk_structure *)

(* Pre_Logic *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

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

(* 并 x∪y = {z:z∈x或者z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* 定义9  x∉y当且仅当x∈y不真 *)
Definition NotIn x y := ~ (x ∈ y).
Notation "x ∉ y" := (NotIn x y) (at level 70).

(* 定义10  ¬x={y：y∉x} *)
Definition Complement x := \{λ y, y ∉ x \}.
Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* 定义13  x~y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).
Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 定义85  x≠y 当且仅当 x=y 不真 *)
Notation "x ≠ y" := (~ (x = y)) (at level 70).

(* 定义15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* 定义18  全域 μ={x:x=x} *)
Definition μ := \{ λ x, x = x \}.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.
Notation "∩ x" := (Element_I x) (at level 66).

(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.
Notation "∪ x" := (Element_U x) (at level 66).

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)
Definition Included x y := ∀ z, z ∈ x -> z ∈ y.
Notation "x ⊂ y" := (Included x y) (at level 70).

(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.
Notation "pow( x )" := (PowerClass x)(at level 0, right associativity).

(* 定义40  [x]={z:如果x∈μ，则z=x} *)
Definition Singleton x := \{ λ z, x ∈ μ -> z = x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

(* 定义45  [x|y]=[x]∪[y] *)
Definition Unordered x y := [x] ∪ [y].
Notation "[ x | y ]" := (Unordered x y) (at level 0).

(* 定义48  [x,y] = [[x]|[x|y]] *)
Definition Ordered x y := [ [x] | [x|y]].
Notation "[ x , y ]" := (Ordered x y) (at level 0).

(* 定义51  z的1st坐标=∩∩z *)
Definition First z := ∩∩z.

(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z)~(∪∩z) *)
Definition Second z := (∩∪z)∪(∪∪z) ~ (∪∩z).

(* 定义56  r是一个关系当且仅当对于r的每个元z存在x与y使得z=[x,y]; 一个关系是一个类，它的元为序偶 *)
Definition Relation r := ∀ z, z ∈ r -> ∃ x y, z = [x,y].

(* { (x,y) : ... } *)
Notation "\{\ P \}\" :=
  (\{ λ z, ∃ x y, z = [x,y] /\ P x y \}) (at level 0).

(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=[x,z],[x,y]∈s同时[y,z]∈r},类r∘s是r与s的合成 *)
Definition Composition r s :=
  \{\ λ x z, ∃ y, [x,y] ∈ s /\ [y,z] ∈ r \}\.
Notation "r ∘ s" := (Composition r s) (at level 50).

(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)
Definition Inverse r := \{\ λ x y, [y,x] ∈ r \}\.
Notation "r ⁻¹" := (Inverse r) (at level 5).

(* 定义63 f是一个函数当且仅当f是一个关系同时对每个x，每个y，每个z，如果 [x,y]∈f 且
   [x，z]∈f，则 y=z。*)
Definition Function f  :=
  Relation f /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z).

(* 定义65 f的定义域={x：对于某个y，[x，y]∈f} *)
Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.
Notation "dom( f )" := (Domain f)(at level 5).

(* 定义66 f的值域={y：对于某个x，[x，y]∈f} *)
Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.
Notation "ran( f )" := (Range f)(at level 5).

(* 定义68 f(x)=∩{y:[x,y]∈f} *)
Definition Value f x := ∩(\{ λ y, [x,y] ∈ f \}).

Notation "f [ x ]" := (Value f x)(at level 5).

(* 定义72 x × y={[u,v]:u∈x/\v∈y} *)
Definition Cartesian x y := \{\ λ u v, u ∈ x /\ v ∈ y \}\.
Notation "x × y" := (Cartesian x y) (at level 2, right associativity).

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x同时f的值域⊂ y} *)
Definition Exponent y x :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)
Definition On f x := Function f /\ dom(f) = x.

(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)
Definition To f y := Function f /\ ran(f) ⊂ y.

(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)
Definition Onto f y := Function f /\ ran(f) = y.

(* 定义81 *)
Definition Rrelation x r y := [x,y] ∈ r.

(* 定义82 *)
Definition Connect r x := ∀ u v, u ∈ x -> v ∈ x
  -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u = v).

(* 定义83 *)
Definition Transitive r x := ∀ u v w, u ∈ x -> v ∈ x -> w ∈ x
  -> Rrelation u r v -> Rrelation v r w -> Rrelation u r w.

(* 定义84 *)
Definition Asymmetric r x := ∀ u v, u ∈ x -> v ∈ x
  -> Rrelation u r v -> ~ Rrelation v r u.

(* 定义86 *)
Definition FirstMember z r x :=
  z ∈ x /\ (∀ y, y ∈ x -> ~ Rrelation y r z).

(* 定义87 *)
Definition WellOrdered r x :=
  Connect r x /\ (∀ y, y ⊂ x -> y ≠ Φ -> ∃ z, FirstMember z r y).

(* 定义89 *)
Definition rSection y r x := y ⊂ x /\ WellOrdered r x
  /\ (∀ u v, u ∈ x -> v ∈ y -> Rrelation u r v -> u ∈ y).

(* 定义93 *)
Definition Order_Pr f r s := Function f
  /\ WellOrdered r dom(f) /\ WellOrdered s ran(f)
  /\ (∀ u v, u ∈ dom(f) -> v ∈ dom(f) -> Rrelation u r v
    -> Rrelation f[u] s f[v]).

(* 定义95 *)
Definition Function1_1 f := Function f /\ Function (f⁻¹).

(* 定义98 *)
Definition Order_PXY f x y r s := WellOrdered r x /\ WellOrdered s y
  /\ Order_Pr f r s /\ rSection dom(f) r x /\ rSection ran(f) s y.

(* 定义103 *)
Definition E := \{\ λ x y, x ∈ y \}\.

(* 定义105 *)
Definition Full x := ∀ m, m ∈ x -> m ⊂ x.

(* 定义106 *)
Definition Ordinal x := Connect E x /\ Full x.

(* 定义112 *)
Definition R := \{ λ x, Ordinal x \}.

(* 定义115 *)
Definition Ordinal_Number x := x ∈ R.

(* 定义116 *)
Definition Less x y := x ∈ y.
Notation "x ≺ y" := (Less x y) (at level 67, left associativity).

(* 定义117 *)
Definition LessEqual (x y: Class) := x ∈ y \/ x = y.
Notation "x ≼ y" := (LessEqual x y) (at level 67, left associativity).

(* 定义122 *)
Definition PlusOne x := x ∪ [x].

(* 定义125 *)
Definition Restriction f x := f ∩ (x × μ).
Notation "f | ( x )" := (Restriction f x) (at level 30).

(* 定义129 *)
Definition Integer x := Ordinal x /\ WellOrdered (E⁻¹) x.

(* 定义130 *)
Definition LastMember x E y := FirstMember x (E⁻¹) y.

(* 定义131 *)
Definition ω := \{ λ x, Integer x \}.

(* 选择函数 *)
Definition ChoiceFunction c :=
  Function c /\ (∀ x, x ∈ dom(c) -> c[x] ∈ x).

(* 定义141 *)
Definition Nest n := ∀ x y, x ∈ n -> y ∈ n -> x ⊂ y \/ y ⊂ x.

(* 定义144 x≈y当且仅当存在一个1-1函数f，f的定义域=x而f的值域=y *)
Definition Equivalent x y :=
  ∃ f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.
Notation "x ≈ y" := (Equivalent x y) (at level 70).

(* 定义148 x是一个基数就是说x是一个序数，并且如果y∈R和y≺x，则x≈y不真 *)
Definition Cardinal_Number x  :=
  Ordinal_Number x /\ (∀ y, y ∈ R -> y ≺ x -> ~ (x ≈ y)).

(* 定义149 C = { x : x 是基数 } *)
Definition C := \{ λ x, Cardinal_Number x \}.

(* 定义151 P = { (x,y) : x ≈ y 且 y ∈ C } *)
Definition P := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

(* 定义166 x是有限的当且仅当P[x]∈w *)
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

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

(* 批处理条件或目标中"与"和"或"策略 *)

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

