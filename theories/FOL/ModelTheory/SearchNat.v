From Coq Require Export Arith Lia.
Require Import PeanoNat.
From Coq Require Import Arith Init.Datatypes.
Require Import Undecidability.FOL.ModelTheory.Core.
Import Nat.

Definition dec (X: Type) : Type := X + (X -> False).
Definition logical_dec (X: Prop): Prop := X \/ (X -> False).
Notation decidable p := (forall x, dec (p x)).
Notation logical_decidable p := (forall x, logical_dec (p x)).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decider p := (forall x, dec (p x)).

Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Notation unique p := (forall x y, p x -> p y -> x = y).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Definition BDP_scheme (domain range: Type) :=
    forall P: domain -> Prop, domain -> exists f: range -> domain,
        (forall n: range, P (f n)) -> forall x, P x.

Definition BDP'_scheme (domain range: Type) :=
    forall P: domain -> Prop, domain -> exists f: range -> domain,
        (exists x, P x) -> (exists m, P (f m)).

Definition BAC_scheme (domain1 domain2 range: Type) :=
    forall R: domain1 -> domain2 -> Prop, (forall x, exists y, R x y) ->
        exists f: domain1 -> range -> domain2, forall n, exists m, R n (f n m).

Notation BDP_on A := (forall domain, @BDP_scheme domain A).
Notation BDP'_on A := (forall domain, @BDP'_scheme domain A).

Notation BDP := (@BDP_on nat).
Notation BDP' := (@BDP'_on nat).

Notation DP := (@BDP_on unit).
Notation DP' := (@BDP'_on unit).

Notation BDP1 := (@BDP_scheme nat unit).
Notation BDP'1 := (@BDP'_scheme nat unit).

Notation CAC := (forall A: Type, @BAC_scheme nat A unit).
Notation BCAC := (forall A: Type, @BAC_scheme nat A nat).
Notation AC00 := (@BAC_scheme nat nat unit).


Definition KS := (forall P: Prop, exists f: nat -> bool, P <-> (exists n, f n = true)).
Definition WPFP := (forall b: nat -> bool, exists a: nat -> bool, (exists n, b n = false) <-> (forall n, a n = true)).
Definition LEM := (forall P, P \/ ~ P).
Definition LPO := (forall f : nat -> bool, (forall x, f x = false) \/ (exists x, f x = true)).
Definition ODC_on A (R: A -> A -> Prop) :=
    forall w,
        exists f : nat -> A, (forall x, exists y, R x y) -> f 0 = w /\ forall n, R (f n) (f (S n)).

Definition DC_on A (R: A -> A -> Prop) :=
    (forall x, exists y, R x y) ->
        exists f : nat -> A, forall n, R (f n) (f (S n)).


Definition DC_root_on A (R: A -> A -> Prop) :=
    (forall x, exists y, R x y) -> forall w,
        exists f : nat -> A, f 0 = w /\ forall n, R (f n) (f (S n)).

Definition PDC_root_on A (R: A -> A -> Prop) :=
    (forall x, exists y, R x y) -> forall w,
        exists f : nat -> A -> Prop, function_rel' f /\ f 0 w /\ forall n, exists x y, f n x /\ f (S n) y /\ R x y.

Notation ODC := (forall A R, @ODC_on A R).
Notation DC := (forall A R, @DC_on A R).
Notation DC_root := (forall A R, @DC_root_on A R).
Notation PDC_root := (forall A R, @PDC_root_on A R).
Notation PDC_on := PDC_root_on.


Inductive reachable {X} (R : X -> X -> Prop) x0 x : Prop :=
| base : R x0 x -> reachable R x0 x
| step y : reachable R x0 y -> R y x -> reachable R x0 x.

Definition reachable' {X} (R : X -> X -> Prop) x0 x :=
  exists f : nat -> X, exists N, f 0 = x0 /\ f (S N) = x /\ forall n, n <= N -> R (f n) (f (S n)).

Lemma reach_reach' {X} (R : X -> X -> Prop) x0 x :
  reachable R x0 x -> reachable' R x0 x.
Proof.
  induction 1.
  - exists (fun n => match n with 0 => x0 | _ => x end), 0. split; trivial. split; trivial.
    intros n. inversion 1; subst. apply H.
  - destruct IHreachable as (f & N & H1 & H2 & H3).
    exists (fun n => if PeanoNat.Nat.leb n (S N) then f n else x), (S N). split. 2: split.
    + rewrite Compare_dec.leb_correct; try lia. apply H1.
    + rewrite Compare_dec.leb_correct_conv; try lia. reflexivity.
    + intros n HN. assert (n <= N \/ n = S N) as [Hn| ->] by lia.
      * rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
      * rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia. now rewrite H2.
Qed.

Lemma DC_with_root :
  DC -> DC_root.
Proof.
  intros H X R HR x0.
  destruct (HR x0) as [y0 Hy0]. pose (a0 := exist _ y0 (@base _ R _ _ Hy0)).
  destruct (H { x | reachable R x0 x } (fun a b => R (proj1_sig a) (proj1_sig b)) ) as [f Hf].
  - intros [x Hx]. destruct (HR x) as [y Hy]. exists (exist _ y (@step _ R x0 y x Hx Hy)). apply Hy.
  - destruct (f 0) as [x Hx] eqn : H0.
    destruct (@reach_reach' _ _ _ _ Hx) as (g & N & H1 & H2 & H3).
    exists (fun n => if PeanoNat.Nat.leb n N then g n else proj1_sig (f (n - N - 1))). split.
    + cbn. apply H1.
    + intros n. assert (n <= N \/ n > N) as [Hn|Hn] by lia.
      * assert (S n <= N \/ n = N) as [Hn'| ->] by lia. 
        -- rewrite ?Compare_dec.leb_correct; try lia. now apply H3.
        -- rewrite Compare_dec.leb_correct, Compare_dec.leb_correct_conv; try lia.
           assert (S N - N - 1 = 0) as -> by lia. rewrite H0. cbn. rewrite <- H2. apply H3. auto.
      * rewrite ?Compare_dec.leb_correct_conv; try lia.
        assert (S n - N - 1 = S (n - N - 1)) as -> by lia. apply Hf.
Qed.

Fact ODC_implies_BDP': ODC -> BDP'.
Proof.
    intros ODC A P a.
    destruct (ODC A (fun x => P) a).
    exists x; intro H'.
    destruct H.
    intro a'; apply H'.
    exists 42.
    apply H0.
Qed.

Lemma CAC_iff_BCAC_AC00:
    CAC <-> BCAC /\ AC00.
Proof.
    split.
    - intros CAC; split.
      + intros A R totalR.
        destruct (CAC A R totalR) as [x Px].
        exists (fun n _ => x n tt).
        intros n; destruct (Px n) as [x' Px'].
        exists 42.
        now destruct x'.
      + exact (CAC nat).
    - intros [BCAC AC00] A R totalR.
      destruct (BCAC A R totalR) as [f Pf].
      destruct (AC00 (fun x y => R x (f x y)) Pf) as [g Pg].
      now exists (fun n t => f n (g n t)).
Qed.

Fact DP_correct: DP <-> (forall A (P: A -> Prop), A -> exists x, P x -> forall x, P x).
Proof.
    split; intros.
    - destruct (H A P); try easy.
      exists (x tt); intro h.
      apply H0. now intros [].
    - intros P a. destruct (H domain P); try easy.
      exists (fun _ => x).
      intros; now apply H0, H1.
Qed.

Fact DP'_correct: DP' <-> (forall A (P : A -> Prop), A -> exists x, (exists x, P x) -> P x).
Proof.
    split; intros.
    - destruct (H A P); try easy.
      exists (x tt); intro h.
      destruct H0 as [[] Pu]; easy. 
    - intros P a. destruct (H domain P); try easy.
      exists (fun _ => x).
      intros. exists tt. now apply H0, H1.
Qed.

Lemma DP_LEM : DP -> LEM.
Proof.
  intros dp P.
  rewrite DP_correct in dp.
  destruct (dp (option (P \/ ~ P)) (fun x => match x with Some x => ~ P | _ => True end) None) as [[x|] H].
  - exact x.
  - right. intros HP. now apply (H I (Some (or_introl HP))).
Qed.

Lemma DP'_LEM : DP' -> LEM.
Proof.
  intros dp P.
  rewrite DP'_correct in dp.
  destruct 
  (dp (option (P \/ ~ P)) 
      (fun x => match x with 
            |Some x => P 
            | _ => False 
            end) 
      None) as [[x|] H].
  - exact x.
  - right. intros HP. apply H. exists (Some (or_introl HP)). exact HP.
Qed.

Lemma DP_LEM' :
  (forall X (p : X -> Prop), X -> exists x, p x -> forall y, p y) -> forall P, P \/ ~ P.
Proof.
  intros dp P. pose (A := { x : unit | P \/ ~ P }).
  destruct (dp (option A) (fun x => match x with Some x => ~ P | _ => True end) None) as [[x|] H].
  - exact (proj2_sig x).
  - right. intros HP. refine (H I (Some _) HP). exists tt. now left.
Qed.

Lemma KS_LPO_LEM: KS -> LPO -> LEM.
Proof.
    intros KS LPO P. 
    destruct (KS P) as [f Pf].
    destruct (LPO f) as [H|H].
    - right; intro p. 
      rewrite Pf in p.
      destruct p as [w Pw].
      specialize (H w).
      congruence.
    - left; now rewrite Pf.
Qed.

Lemma BDP_LPO_LEM : BDP -> LPO -> LEM.
Proof.
    intros dp lpo P.
    destruct (dp (option (P \/ ~ P)) (fun x => match x with Some x => ~ P | _ => True end) None) as [f H].
    destruct (lpo (fun n => if f n then true else false)) as [Hf|[x Hx]].
    - right. intros HP. refine (H _ (Some (or_introl HP)) HP).
        intros n. specialize (Hf n). destruct (f n); try discriminate. trivial.
    - destruct (f x); try discriminate. trivial.
Qed.

Lemma BDP_nat_LPO: BDP1 -> LPO.
Proof.
    intros dp f. 
    specialize (dp (fun n => f n = false)).
    destruct dp; [exact 42|].
    destruct (f (x tt)) eqn: E.
    - right. now exists (x tt).
    - left.  apply H. now intros [].
Qed.

Definition IP :=
    forall (A:Type) (P:A -> Prop) (Q:Prop),
        inhabited A ->
            (Q -> exists x, P x) -> exists x, Q -> P x.

Definition BIP :=
    forall (A:Type) (P:A -> Prop) (Q:Prop),
        inhabited A ->
            (Q -> exists x, P x) -> exists (f: nat -> A), Q -> (exists m, P (f m)).

Fact DC_IP_implies_ODC: DC -> IP -> ODC.
Proof.
    intros DC IP A R w.
    specialize (DC_with_root DC) as DC_root.
    apply IP. 
    constructor; exact (fun _ => w).
    intros DC'%(DC_root A R).
    apply DC'.
Qed.

Goal DP' -> IP.
Proof.
    intros.
    intros A P Q [] HP.
    destruct (H A P X). 
    exists (x tt); intros Q'%HP.
    destruct H0 as [[] P']; easy.
Qed.

Goal IP -> DP'.
Proof.
    intros IP A P.
    intros IA.
    destruct (IP A P (exists x, P x)).
    now constructor.
    easy.
    exists (fun v => x).
    intros P'. exists tt. now apply H.
Qed.

Goal BDP' -> BIP.
Proof.
    intros BDP' A P Q [] HP.
    destruct (BDP' A P X).
    exists x; intros Q'%HP.
    now apply H.
Qed.

Goal BIP -> BDP'.
Proof.
    intros BIP A P a.
    destruct (BIP A P (exists x, P x)). { now constructor. }
    easy.
    now exists x.
Qed.

Section Least_witness.

    Definition nat_eqdec : eqdec nat.
    Proof.
    intros x y.
    destruct (Nat.eq_dec x y) as [H|H].
    - left. exact H.
    - right. exact H.
    Defined.

    Implicit Types (n k: nat).

    Definition safe (p: nat -> Prop) n := forall k, p k -> k >= n.
    Definition least (p: nat -> Prop) n := p n /\ safe p n.

    Fact least_unique (p: nat -> Prop) :
    unique (least p).
    Proof.
    intros x y [H1 H2] [H3 H4].
    enough (x <= y /\ y <= x) by lia. split.
    - apply H2, H3.
    - apply H4, H1.
    Qed.

    Fact safe_O p :
    safe p 0.
    Proof.
    intros k _. lia.
    Qed.

    Fact safe_S p n :
    safe p n -> ~p n -> safe p (S n).
    Proof.
    intros H1 H2 k H3.
    specialize (H1 k H3).
    enough (k <> n) by lia.
    intros ->. easy.
    Qed.

    Definition XM := forall P, P \/ ~P.

    Fact xm_least_safe :
    XM -> forall p n, ex (least p) \/ safe p n.
    Proof.
    intros H p.
    induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [IH|IH].
        + left. exact IH.
        + specialize (H (p n)) as [H|H].
        * left. exists n. easy.
        * right. apply safe_S; assumption.
    Qed.

    Fact least_safe_ex_least :
    (forall p n, ex (least p) \/ safe p n) -> forall p, ex p -> ex (least p).
    Proof.
    intros H p [n H1].
    specialize (H p n) as [H|H].
    * exact H.
    * exists n. easy.
    Qed.

    Fact XM_ex_least:
        XM -> forall p, ex p -> ex (least p).
    Proof.
        intro; now apply least_safe_ex_least, xm_least_safe.
    Qed.

    Fact Logical_dec_safe (P: nat -> Prop):
        (forall n, P n \/ ~ P n) -> forall n, ex (least P) \/ safe P n.
    Proof.
        intros H n.
        induction n as [|n IH].
        - right. apply safe_O.
        - destruct IH as [IH|IH].
        + left. exact IH.
        + specialize (H n) as [H|H].
            * left. exists n. easy.
            * right. apply safe_S; assumption.
    Qed.

    Fact logical_dec_least (P: nat -> Prop):
        (forall n, P n \/ ~ P n) -> ex P -> ex (least P).
    Proof.
        intros H [y Py].
        destruct (@Logical_dec_safe _ H y) as [H'|H'].
        - easy.
        - exists y. split; easy.
    Qed.

End Least_witness.

Section WO.

    Implicit Types n k: nat.
    Variable p: nat -> Prop.
    Variable p_dec: decidable p.

    Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

    Lemma T_base n :
        p n -> T n.
    Proof.
        intros H. constructor. intros H1. destruct (H1 H).
    Qed.

    Lemma T_step n :
        T (S n) -> T n.
    Proof.
        intros H. constructor. intros _. exact H.
    Qed.

    Lemma T_zero n :
        T n -> T 0.
    Proof.
        induction n as [|n IH].
        auto. intros H. apply IH. apply T_step, H.
    Qed.

    Lemma V n :
        p n -> T 0.
    Proof.
        intros H. eapply T_zero, T_base, H.
    Qed.

    Lemma W' :
        forall n, T n -> sig p.
    Proof.
        refine (fix F n a {struct a} := let (phi) := a in
                            match p_dec n with
                            inl H => _ | inr H => _
                            end).
        exact (Sig p n H). exact (F (S n) (phi H)).
    Qed.

    Theorem W :
        ex p -> sig p.
    Proof.
        intros H. apply W' with 0.
        destruct H as [n H]. apply V with n, H.
    Qed.

End WO.

Section DC_search_over_nat.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Hypothesis sur: forall n, exists m, f m = n.

    Lemma exists_next:
    (forall x, exists y, R x y) ->
        Σ f: nat -> B, forall b, exists n, R b (f n).
    Proof.
        intro total; exists f; intro b.
        destruct (total b) as [c Rbc], (sur c) as [m p].
        exists m. now rewrite p.
    Qed.

    Lemma DC_ω:
        (forall x y, dec (R x y)) -> (@DC_root_on B R).
    Proof.
        intros dec__R total root.
        destruct (exists_next total) as [h P].
        assert(forall b, decidable (fun n : nat => R b (h n))) as dec__R' by easy.
        specialize (fun b => (@W (fun n => R b (h n)) (dec__R' b) (P b))) as WO.
        exists (fix g n := match n with O => root | S n => h (pi1 (WO (g n))) end).
        split; try easy; intro n; cbn.
        destruct (WO ((fix g n:= match n with 0 => root |S n' => h (pi1 (WO (g n'))) end) n)); easy.
    Qed.

End DC_search_over_nat.

Section AC_ω_implies_DC.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Variable g: B -> nat.
    Hypothesis bi_l: forall n, g (f n) = n.
    Hypothesis bi_r: forall n, f (g n) = n.
    Hypothesis AC_ω: AC_ω.

Lemma DC_ω': (@DC_root_on B R).
Proof.
    intros total_B w.
    destruct (@AC_ω nat (fun n m => R (f n) (f m))) as [h Hh].
    - intro n. specialize (total_B (f n)) as [fm Pfm].
      exists (g fm). now rewrite bi_r.
    - exists (fun n => f (iter n h (g w))); split.
      + now cbn; rewrite bi_r.
      + intro n; cbn. apply Hh.
Qed. 

End AC_ω_implies_DC.

Section DC_pred_least_over_nat.

    Variable B: Type.
    Variable R:  B -> B -> Prop.
    Variable f: nat -> B.
    Variable g: B -> nat.
    Hypothesis bij_l: forall n, g (f n) = n.
    Hypothesis bij_r: forall b, f (g b) = b.
    Hypothesis logical_dec__R': forall x y, logical_dec (R x y).

    Fixpoint least_pred w n b :=
        match n with
        | O => b = w
        | S n => exists! bn, least_pred w n bn /\ least (fun x => R bn (f x)) (g b)
        end.

    Lemma exists_next_pred:
        (forall x, exists y, R x y) ->
            forall b, exists n, least (fun n => R b (f n)) n. 
    Proof.
        intros total__R b.
        destruct (total__R b) as [next Rbnext].
        apply logical_dec_least. {now intro n; specialize (logical_dec__R' b (f n)). }
        exists (g next).
        now rewrite bij_r.
    Qed.

    Lemma functional_least_pred root:
        (forall x, exists y, R x y) ->
            function_rel' (least_pred root).
    Proof.
        intros total__R n; induction n.
        - exists root; constructor; cbn; try easy.
        - destruct IHn as [v [p1 p2]].
        destruct (exists_next_pred total__R v) as [next Rrn].
        exists (f next); split; try easy; cbn.
        exists v; constructor; try easy. 
        split; try easy.
        now rewrite bij_l.
        intros v' [p _]; now apply p2.
        intros fnext' (p1' & p2' & p3).
        enough (g (f next) = g fnext').
        rewrite bij_l in H. rewrite H. easy.
        specialize(p3 p1' p2').
        unshelve eapply least_unique.
        exact (fun x : nat => R p1' (f x)).
        destruct p2' as [H1 H2].
        rewrite (p2 _ H1) in Rrn.
        now rewrite bij_l. easy.
    Qed.

    Lemma root_least_pred root: least_pred root O root.
    Proof.
        now intros.
    Qed.

    Lemma successor_least_pred root:
        (forall x, exists y, R x y) ->
            (forall n, exists x y, least_pred root n x /\ least_pred root (S n) y /\ R x y).
    Proof.
        intro total__R; induction n; cbn.
        - exists root.
        destruct (exists_next_pred total__R root) as [next Rrn].
        exists (f next); split; try easy; split.
        + rewrite bij_l; exists root; constructor; easy.
        + now destruct Rrn as (a_name & _).
        - destruct IHn as (x & y & nx & [bn [P1 P2]] & R'xy); exists y.
        destruct (exists_next_pred total__R y) as [next Rrn].
        exists (f next); split; try easy.
        exists bn; constructor; easy.
        split. 2: { now destruct Rrn. }
        exists y; constructor.
        split. exists bn; now constructor.
        now rewrite bij_l.
        intros y' ([b' [P1' P1'']] & P2').
        rewrite bij_l in P2'.
        enough (g y = g y'). { rewrite <- (bij_r y), <- (bij_r y'); now f_equal. }
        unshelve eapply least_unique.
        exact  (fun x : nat => R b' (f x)).
        destruct P1; destruct P1'.
        destruct (functional_least_pred root total__R n) as [x_n [_ uni_x]].
        enough (bn = b') as re. now rewrite <- re. 
        now rewrite <- (uni_x bn), <- (uni_x b').
        easy.
    Qed.

Theorem DC_pred_ω: @PDC_root_on B R.
Proof.
    intros total w.
    exists(least_pred w); split.
    - exact (functional_least_pred w total).
    - split; exact(root_least_pred w) + exact(successor_least_pred w total).
Qed.

End DC_pred_least_over_nat.

Section StrongInduction.

    Definition strong_induction (p: nat -> Type) :
    (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
    Proof.
        intros H x; apply H.
        induction x; [intros; lia| ].
        intros; apply H; intros; apply IHx; lia.
    Defined.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.

Section Cantor.

    Definition next a : nat * nat :=
        match a with
        | (0,y) => (S y, 0)
        | (S x, y) => (x, S y)
        end.

    Fixpoint decode n : nat * nat :=
        match n with
        | 0 => (0,0)
        | S n' => next (decode n')
        end.

    Fixpoint sum n : nat :=
        match n with
        | 0 => 0
        | S n' => S n' + sum n'
        end.

    Definition encode_p '(x, y) : nat :=
        sum (x + y) + y.

    Fact encode_next a :
        encode_p (next a) = S (encode_p a).
    Proof.
        destruct a as [[|x] y]; cbn -[sum].
        - rewrite !add_0_r. rewrite add_comm. reflexivity.
        - rewrite !add_succ_r. reflexivity.
    Qed.

    Opaque encode_p. 

    Fact encode_decode n :
        encode_p (decode n) = n.
    Proof.
    induction n as [|n IH]; cbn.
    - reflexivity.
    - rewrite encode_next, IH. reflexivity.
    Qed.

    Fact decode_encode a :
        decode (encode_p a) = a.
    Proof.
    revert a.
    enough (forall n a, encode_p a = n -> decode n = a) by eauto.
    induction n as [|n IH]; intros [x y]; cbn.
    - destruct x, y; cbn [encode_p]; cbn; easy.
    - destruct y.
        + destruct x.
        * discriminate.
        * change (S x, 0) with (next (0,x)).
            rewrite encode_next.
            intros [= <-].
            f_equal. apply IH. reflexivity.
        + change (x, S y) with (next (S x, y)). 
        rewrite encode_next.
        intros [= <-].
        f_equal. apply IH. reflexivity.
    Qed.

    Definition encode a b := encode_p (a, b).
    Definition π__1 x := fst (decode x).
    Definition π__2 x := snd (decode x).

    Lemma cantor_paring: forall x, encode (π__1 x) (π__2 x) = x.
    Proof.
        intro x; unfold encode, π__1, π__2.
        rewrite <- (surjective_pairing (decode x)).
        now rewrite encode_decode.
    Qed.

    Lemma cantor_left: forall x y, π__1 (encode x y) = x.
    Proof.
        intros x y; unfold encode, π__1.
        now rewrite decode_encode.
    Qed.

    Definition cantor_right: forall x y, (π__2 (encode x y)) = y.
    Proof.
        intros x y; unfold encode, π__2.
        now rewrite decode_encode.
    Qed.

End Cantor.







