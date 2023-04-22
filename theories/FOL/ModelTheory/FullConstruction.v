Require Import Undecidability.FOL.Completeness.TarskiCompleteness.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Lia Peano_dec.
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

Section From_BDP_and_DC.

    Hypothesis BDP: BDP.
    Hypothesis BDP': BDP'.
    Hypothesis DC: DC.
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.


End From_BDP_and_DC.


End AnyModel.