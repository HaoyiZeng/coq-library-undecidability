Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Lia Peano_dec.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullHenkinModel.
Require Import Undecidability.FOL.ModelTheory.DCFull.

Local Set Implicit Arguments.

Section Incl_im.
    Variables A B C: Type.

    Definition im_sub (ρ: A -> C) (ρ': B -> C)  := forall x, exists y, ρ x = ρ' y.
    Definition im_sub_k (ρ: nat -> C) (ρ': B -> C)  k := forall x, x < k -> exists y, ρ x = ρ' y.

End Incl_im.

Notation "ρ ⊆ ρ'" := (im_sub ρ ρ') (at level 25).
Notation "ρ ⊆[ k ] ρ'" := (im_sub_k ρ ρ' k) (at level 25).

Section Incl_facts.

    Lemma bounded_cantor b:
    Σ E, forall x, x < b -> π__1 x < E.
    Proof.
        clear; strong induction b.
        specialize (H (pred b)).
        destruct b; [exists 0; intros; lia| ].
        destruct H as [Ep EP]; [lia |].
        destruct (lt_dec Ep ((π__1 b))); 
        exists (S (π__1 b)) + exists (S Ep); 
        intros x H'; destruct (lt_dec x b); specialize (EP x); 
        lia || now assert (x = b) as -> by lia; lia.
    Qed.

    Lemma refl_sub {A B} (e: A -> B): e ⊆ e.
    Proof.
        intros x.
        now exists x.
    Qed.

    Lemma trans_sub  {A B} (a b c: A -> B): a ⊆ b -> b ⊆ c -> a ⊆ c.
    Proof.
        unfold "⊆"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

End Incl_facts.


Section AnyModel.
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 

Section Henkin_condition.
    Definition succ (ρ: env M) (ρ_s: env M) (φ: form): Prop :=
        ((forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ)) 
            /\ 
        (M ⊨[ρ] (∃ φ) -> exists m, M ⊨[ρ_s m .: ρ] φ).
End Henkin_condition.

Notation "ρ ⇒ ρ_s" := (forall φ, succ ρ ρ_s φ) (at level 25).
Notation "ρ ⇒[ phi ] ρ_s" := (succ ρ ρ_s phi) (at level 25).

Section Technical_lemma.

    Lemma map_cons_w (ρ ρ': env M) w  {n} (v: vec term n): 
    (forall t : term, In t v -> t ₜ[ M] ρ' = t`[fun x : nat => $(S x)] ₜ[ M] (w .: ρ') )
        -> map (eval M interp' ρ') v = map (eval M interp' (w .: ρ')) (map (subst_term (fun x : nat => $(S x))) v).
    Proof.
        intro H.
        induction v; cbn. {constructor. }
        rewrite IHv, (H h). {easy. }
        constructor.
        intros t H'; apply H.
        now constructor.
    Qed.

    Lemma cons_w (ρ ρ': env M) (σ: nat -> term) w:
        forall x, (σ >> eval M interp' ρ') x = (σ >> subst_term ↑) x ₜ[ M] (w .: ρ').
    Proof.
        unfold ">>".
        intro x; induction (σ x); cbn; try easy.
        now rewrite map_cons_w with (w := w).
    Qed.
    
    Lemma im_bounded_sub (ρ ρ': env M) b:
        ρ ⊆[b] ρ' -> exists (ξ : nat -> nat), forall x, x < b -> (ρ x) = (ρ' (ξ x)).
    Proof.
        induction b; cbn; [intros |].
        - exists (fun _ => O); lia.
        - intros.
        destruct IHb as [ξ Pξ].
        intros x Hx; apply (H x); lia. 
        destruct (H b) as [w Hw]; [lia|].
        exists (fun i => if (eq_nat_dec i b) then w else (ξ i)).
        intros; destruct (eq_nat_dec x b) as [->| eH]; [easy|].
        eapply Pξ; lia.  
    Qed.

    Lemma im_bounded_sub_form ρ ρ' φ k: bounded k φ -> ρ ⊆[k] ρ' -> 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros H H'.
        destruct (@im_bounded_sub _ _ _ H') as [ξ Hξ].
        exists (fun x => $ (ξ x)); split.
        - rewrite sat_comp.  
        apply bound_ext with k. exact H.
        intros. cbn. now apply Hξ.
        -  cbn. intros x Hx. now rewrite Hξ.
    Qed.

    Lemma bounded_sub_impl_henkin_env ρ ρ' ρ_s: 
        ρ' ⇒ ρ_s -> forall φ k, bounded k φ -> ρ ⊆[k] ρ' -> 
        ρ ⇒[φ] ρ_s.
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (im_bounded_sub_form HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [P _].
        split.
        + intro Hp; rewrite fH.
        apply P; revert Hp.
        intros H' n'.
        rewrite sat_comp.
        unshelve eapply (bound_ext _ H). exact (ρ_s n' .: ρ). 
        intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        now rewrite (cons_w ρ ρ' σ (ρ_s n')).
        lia.
        apply H'.
        + assert (bounded k (∃ φ)) as HS'.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (im_bounded_sub_form HS' Ink ) as (σ' & fH' & EH').
        specialize (Rρ' (φ[up σ'])) as [_ P'].
        rewrite fH'; intro Hp.
        destruct (P' Hp) as [w Hw].
        apply P' in Hp. 
        exists w; revert Hw; rewrite sat_comp.
        apply (bound_ext _ H).
        intros x HL.
        induction x. cbn. easy. cbn. 
        rewrite <- EH'.
        now rewrite (cons_w ρ ρ' σ' (ρ_s w)).
        lia.
    Qed.

End Technical_lemma.

Section Recursive_def.

    Variable F: nat -> nat -> M.
    Hypothesis path: forall n, F n ⇒ F (S n) /\ F n ⊆ F (S n).

    Lemma mono_F' a b: F a ⊆ F (a + b) .
    Proof.
        induction b.
        - assert (a + 0 = a) as -> by lia; apply refl_sub.
        - assert (a + S b = S(a + b)) as -> by lia.
          eapply trans_sub. exact IHb. apply path.
    Qed.

    Lemma mono_F a b: a < b -> F a ⊆ F b.
    Proof.
        assert (a < b -> Σ c, a + c = b) .
        intro H; exists (b - a); lia.
        intro aLb.
        destruct (H aLb) as [c Pc].
        specialize (mono_F' a c).
        now rewrite Pc. 
    Qed.

    Opaque encode_p. 

    Definition ι x := F (π__1 x) (π__2 x).

    Lemma ι_incl n: F n ⊆ ι.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold ι.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma ι_succ n: F n ⇒ ι.
    Proof.
        split; intros; destruct (path n) as [P _];
        destruct (P φ) as [H1 H2];
        specialize (ι_incl (S n)) as Pws.
        - apply H1.
          intro n'; destruct (Pws n') as [w ->]. 
          apply H.
        - destruct (H2 H) as [w Hw].
          destruct (Pws w) as [x ->] in Hw.
          now exists x.
    Qed.

    Lemma bounded_sub b: 
        exists E: nat, ι ⊆[b] (F E).
    Proof.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros x H.
        unfold ι.
        specialize (PE _ H).
        specialize (mono_F  PE) as H1.
        destruct (H1 (π__2 x)) as [w Hw].
        now exists w.
    Qed.

    Fact Fixed_point': ι ⊆ ι.
    Proof.
        apply refl_sub.
    Qed.

    Theorem Fixed_point: ι ⇒ ι.
    Proof.
        intros.
        destruct (find_bounded φ) as [b bφ].
        destruct (bounded_sub b) as [E P].
        unshelve eapply bounded_sub_impl_henkin_env; [exact (F E) |exact b|..]; try easy.
        apply (ι_succ E).
    Qed.

End Recursive_def.

Section BDC.

Definition merge {A: Type} (f1 f2: nat -> A): nat -> A :=
    fun n => match EO_dec n with 
        | inl L => f1 (projT1 L)
        | inr R => f2 (projT1 R)
    end.

Fact merge_l: forall {A: Type} (f1 f2: nat -> A), (f1 ⊆ merge f1 f2).
Proof.
    intros A f1 f2 x; exists (2*x).
    assert (even (2*x)) by (exists x; lia).
    unfold merge; destruct (EO_dec (2*x)).
    enough (pi1 e = x) as -> by easy; destruct e; cbn; lia.
    exfalso; apply (@EO_false (2*x)); split; easy.
Qed.

Fact merge_r: forall {A: Type} (f1 f2: nat -> A), (f2 ⊆ merge f1 f2).
Proof.
    intros A f1 f2 x; exists (2*x + 1).
    assert (odd (2*x + 1)) by (exists x; lia).
    unfold merge; destruct (EO_dec (2*x + 1)).
    exfalso; apply (@EO_false (2*x + 1)); split; easy.
    enough (pi1 o = x) as -> by easy; destruct o; cbn; lia.
Qed.

Fact merge_ex: forall {A: Type} (f1 f2: nat -> A), 
    forall x, exists y, f1 y = merge f1 f2 x \/ f2 y = merge f1 f2 x.
Proof.
    intros A f1 f2 x; unfold merge.
    destruct (EO_dec x) as [[i Hi]|[i Hi]]; now exists i; (left + right). 
Qed.

Fixpoint folding {A: Type} {n: nat} (init: nat -> A) (v: vec (nat -> A) n) :=
    match v with
    | nil _ => init
    | cons _ f n v => merge f (folding init v)
    end.

Fact init_in_folding {A: Type} {n: nat} (init: nat -> A) (v: vec (nat -> A) n) :
    init ⊆ folding init v.
Proof.
    induction v; cbn.
    - apply refl_sub.
    - eapply trans_sub.
      apply IHv.
      apply merge_r.
Qed.

Fact folding_incl {A: Type} {n: nat} (init: nat -> A):
    forall v: vec (nat -> A) n, forall i, In i v -> i ⊆ folding init v.
Proof.
    intros; induction H; cbn.
    + apply merge_l.
    + eapply trans_sub. exact IHIn. apply merge_r. 
Qed.

Definition succ_vec (n: nat) (init: env M) (ρ_vec: vec (env M) n) (ρ_s: env M) (φ: form): Prop :=
    let ρ := folding init ρ_vec in
    ((forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ)) 
        /\ 
    (M ⊨[ρ] (∃ φ) -> exists m, M ⊨[ρ_s m .: ρ] φ).

    Definition BDC:=
        forall (A: Type) (R: forall {n}, vec A n -> A -> Prop), 
            A -> (forall n (v: vec A n), exists w, R v w) ->
            (exists f: nat -> A, forall n (v: vec nat n), exists m, R (map f v) (f m)).

    Definition BCAC := forall B (R: nat -> B -> Prop), (forall x, exists y, R x y) -> exists f: (nat -> B), 
        forall n, exists w, R n (f w).

    Hypothesis BDP: BDP.
    Hypothesis BDP': BDP'.
    Hypothesis BDC : BDC.
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    Hypothesis BCAC: BCAC.

    Lemma BCAC_term:
        forall B (R: form -> B -> Prop), (forall x, exists y, R x y) -> exists f: (nat -> B), 
        forall n, exists w, R n (f w).
    Proof.
        intros B R totalR.
        destruct (@BCAC B (fun n => R (phi_ n))) as [g Pg].
        intro x. apply (totalR (phi_ x)).
        exists g. intro n. 
        specialize (Pg (nth_ n)).
        now rewrite Hphi in Pg.
    Qed.

    Definition universal_witness:
        forall ρ, exists (W: nat -> M), forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ.
    Proof.
        intros ρ.
        destruct (@BCAC_term (nat -> M) (fun phi h => (forall w, M ⊨[(h w) .: ρ] phi) -> M ⊨[ρ] (∀ phi))) as [F PF].
        - intro φ; destruct (BDP (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          exact (ρ (nth_ φ)). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
          intro φ; specialize (PF φ).
          intro H'. destruct PF as [[] PF]; apply PF.
          intro w.
          specialize (H' (encode 0 w)).
          now rewrite cantor_left, cantor_right in H'.
          intro w. specialize (H' (encode (S n) w)).
          now rewrite cantor_left, cantor_right in H'.
    Qed.

    Definition existential_witness:
        forall ρ, exists (W: nat -> M), forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ).
    Proof.
        intros ρ.
        destruct (@BCAC_term (nat -> M) (fun phi h =>  M ⊨[ρ] (∃ phi) -> (exists w, M ⊨[(h w) .: ρ] phi))) as [F PF].
        - intro φ; destruct (BDP' (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
          intro φ; specialize (PF φ).
          intro H'. destruct PF as [[] PF]. 
          destruct (PF H') as [w Pw].
          exists (encode 0 w).
          now rewrite cantor_left, cantor_right.
          destruct (PF H') as [w Pw].
          exists (encode (S n) w).
          now rewrite cantor_left, cantor_right.
    Qed.

    Lemma Henkin_witness:
        forall ρ, exists (W: nat -> M), 
            (forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ)  
                /\ 
            (forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ)).
    Proof.
        intros ρ.
        destruct (universal_witness ρ) as [Uw PUw].
        destruct (existential_witness ρ) as [Ew PEw].
        exists (merge Uw Ew); split; intros φ Hφ.
        - apply PUw; intro w.
          destruct (merge_l Uw Ew w) as [key ->].
          apply (Hφ key). 
        - destruct (PEw _ Hφ) as [w Pw].
          destruct (merge_r Uw Ew w) as [key Hk].
          exists key. now rewrite <- Hk.
    Qed.

    Definition Henkin_succ {n} (init: env M) (v: vec (env M) n) ρ :=
        (forall φ, succ_vec init v ρ φ) /\ init ⊆ ρ /\ forall ρ', In ρ' v -> ρ' ⊆ ρ.

Lemma totality_Henkin_vec: forall {n: nat} (init: env M) (ρ_vec: vec _ n), exists ρ_s, Henkin_succ init ρ_vec ρ_s.
Proof.
    intros.
        pose (ρ := folding init ρ_vec).
        destruct (Henkin_witness ρ) as [W [P1 P2]].
        exists (merge ρ W); split; [split|split].
        - specialize (P1 φ) as Pw.
        intros H' w'.
        apply Pw; intro w.
        now destruct (merge_r ρ W w) as [key ->].
        - specialize (P2 φ) as Pw.
        intros H'%Pw.
        destruct H' as [w Hw].
        destruct (merge_r ρ W w) as [key Hk].
        exists key. now rewrite <- Hk.
        - eapply trans_sub.
          apply (init_in_folding init ρ_vec).
          apply merge_l.
        - intros i Ini.
          assert (i ⊆ ρ) as H1 by now eapply folding_incl.
          assert (ρ ⊆ merge ρ W) as H2 by apply merge_l.
          eapply (trans_sub H1 H2).
Qed.

Lemma countable_domain init:
    exists f: nat -> (nat -> M),
        forall n (v: vec nat n), exists k, Henkin_succ init (map f v) (f k).
Proof.
    destruct (@BDC (env M) (fun n v s => Henkin_succ init v s) init) as [f Hf].
    intros n v; destruct (totality_Henkin_vec init v) as [w Hw].
    exists w; apply Hw.
    exists f; exact Hf.
Qed.

End BDC.

Section new_Recursive_def.

    Variable init: nat -> M.
    Variable F: nat -> nat -> M.
    Hypothesis domain: forall n (v: vec nat n), exists k, Henkin_succ init (map F v) (F k).

    Opaque encode_p. 

    Definition ι' x := F (π__1 x) (π__2 x).

    Lemma ι'_incl n: F n ⊆ ι'.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold ι'.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma trans_succ a b c:
        (a ⇒ b /\ a ⊆ b) -> (b ⇒ c /\ b ⊆ c) -> (a ⇒ c /\ a ⊆ c).
    Proof.
        intros [H1 S1] [H2 S2]; split; [intro φ| ].
        destruct (H1 φ) as [H11 H12], (H2 φ) as [H21 H22];
        split; intro H.
        - apply H11. intro n. destruct (S2 n) as [w ->]. apply H.
        - destruct (H12 H) as [w Hw].
          destruct (S2 w) as [w' Hw'].
          exists w'. rewrite <- Hw'.
          easy.
        - eapply (trans_sub S1 S2).
    Qed.
    
    Lemma ι'_succ n: F n ⇒ ι'.
    Proof.
        intro φ.
        destruct (find_bounded φ) as [y Hy].
        unshelve eapply bounded_sub_impl_henkin_env.
        exact (merge (F n) init).
        exact y.
        destruct (@domain 1 (cons _ n 0 (nil _))) as [k [Pk _]].
        intro phi; destruct (Pk phi) as [H1 H2].
        split; intro H.
        - apply H1. intro x; destruct (ι'_incl k x) as [w ->]; apply H.
        - destruct (H2 H) as [w Hw]. destruct (ι'_incl k w) as [w' Hw'].
          exists w'. now rewrite <- Hw'.
        - trivial.
        - intros x' _.
          apply merge_l.
    Qed.    

    Fixpoint n_vec n :=
        match n with
        | O => nil _
        | S n => cons _ n n (n_vec n)
        end.

    Lemma In_by_map {A B: Type} {n} (f: A -> B) a (v: vec A n):
        In a v -> In (f a) (map f v).
    Proof.
        induction 1; cbn; now constructor.
    Qed.

    Lemma In_n_vec n:
        forall a, a < n -> In a (n_vec n).
    Proof.
        induction n; cbn.
        - lia.
        - intros x Hx. 
        assert (x = n \/ x < n) as [->| H1] by lia.
            + constructor.
            + constructor. now apply IHn. 
    Qed.
    
    Lemma new_bounded_sub b: 
        exists E: nat, ι' ⊆[b] (F E).
    Proof.
        destruct (bounded_cantor b) as [E PE].
        destruct(@domain E (n_vec E)) as [K [_ Hk]].
        exists K; intros x H.
        unfold ι.
        specialize (PE _ H).
        unfold ι'.
        enough (In (F (π__1 x)) (map F (n_vec E))) as H1.
        apply Hk in H1.
        exact (H1 (π__2 x)).
        apply In_by_map.
        apply In_n_vec.
        easy.
    Qed.

    Theorem new_Fixed_point: ι' ⇒ ι'.
    Proof.
        intros.
        destruct (find_bounded φ) as [b bφ].
        destruct (new_bounded_sub b) as [E P].
        unshelve eapply bounded_sub_impl_henkin_env; [exact (F E) |exact b|..]; try easy.
        apply (ι'_succ E).
    Qed.

End new_Recursive_def.


Section From_BDP_and_DC.

    Hypothesis BDP: BDP.
    Hypothesis BDP': BDP'.
    Hypothesis DC: DC.
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    Theorem BCAC_: BCAC.
     Proof.
       intros A R H0.
       set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
       destruct (H0 0) as (y0,Hy0).
       specialize (DC_with_root DC) as DC'.
       destruct (@DC' (prod nat A)) with(R:=R') (w:=(0,y0)) as (f,(Hf0,HfS)).
       - intro x; destruct (H0 (fst x)) as (y,Hy).
         exists (S (fst x),y).
         red. auto.
       - assert (Heq:forall n, fst (f n) = n).
         + induction n.
           * rewrite Hf0; reflexivity.
           * specialize HfS with n; destruct HfS as (->,_); congruence.
         + exists (fun n => snd (f (S n))).
           intro n'. specialize HfS with n'.
           destruct HfS as (_,HR).
           rewrite Heq in HR.
           exists n'; assumption.
     Qed.

    (* Definition AC_form: BAC_form.
    Proof.
        intros A R total_R.
        set (R' n := R (phi_ n)).
        assert (forall x, exists y, R' x y) as total_R'. intro x. 
        now destruct (total_R (phi_ x)) as [b Pb]; exists b.
        destruct (CAC total_R') as [f Pf].
        exists (fun fm => f (nth_ fm)).
        intro x; specialize (Pf (nth_ x)).
        unfold R' in Pf.
        now rewrite (Hphi x) in Pf.
    Qed. *)

    Lemma totality_Henkin: 
        forall ρ, exists ρ_s, ρ ⇒ ρ_s /\ ρ ⊆ ρ_s.
    Proof.
        intro ρ.
        destruct (Henkin_witness BDP BDP' Hphi BCAC_ ρ) as [W [P1 P2]].
        exists (merge ρ W); split; [split|].
        - specialize (P1 φ) as Pw.
        intros H' w'.
        apply Pw; intro w.
        now destruct (merge_r ρ W w) as [key ->].
        - specialize (P2 φ) as Pw.
        intros H'%Pw.
        destruct H' as [w Hw].
        destruct (merge_r ρ W w) as [key Hk].
        exists key. now rewrite <- Hk.
        - apply merge_l.
    Qed.

    Theorem path_ex:
        exists F: nat -> (env M), forall n, F n ⇒ F (S n) /\ F n ⊆ F (S n).
    Proof.
        eapply (@DC (env M) (fun x y => x ⇒ y /\ x ⊆ y)).
        apply totality_Henkin.
    Qed.

End From_BDP_and_DC.

End AnyModel.

Section Result.

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_: nat -> form.
    Variable nth_: form -> nat.
    Hypothesis Hphi: forall phi, phi_ (nth_ phi) = phi.

    Theorem LS_downward:
        BDP -> BDP' -> DC -> forall (M: model), 𝕋 ⪳ M.
    Proof.
        intros BDP BDP' DC M.
        specialize (DC_with_root DC) as DC'.
        destruct (path_ex BDP BDP' DC Hphi) as [F PF].
        pose (Fixed_point PF) as Succ.
        specialize Henkin_env_el with (phi_ := phi_) (h := ι F) as [N PN].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        now exists N, (morphism (ι F)).
    Qed.

End Result.

Section Result2.

    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_: nat -> form.
    Variable nth_: form -> nat.
    Hypothesis Hphi: forall phi, phi_ (nth_ phi) = phi.

    Theorem new_LS_downward:
        BDP -> BDP' -> BDC -> forall (M: model), M -> 𝕋 ⪳ M.
    Proof.
        intros BDP BDP' BDC M m.
        rewrite BDC_BDC_list in BDC.
        specialize (BDC_CAC BDC) as BCAC.
        rewrite <- BDC_BDC_list in BDC.
        destruct (countable_domain BDP BDP' BDC Hphi BCAC (fun _=>m)) as [F PF].
        pose (new_Fixed_point PF) as Succ.
        specialize Henkin_env_el with (phi_ := phi_) (h := ι F) as [N PN].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        now exists N, (morphism (ι F)).
    Qed.

End Result2.


