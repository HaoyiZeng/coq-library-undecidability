Require Import Undecidability.FOL.ModelTheory.Core.
Require Import Coq.Arith.Compare_dec.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.HenkinModel.


Notation "'Σ' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
        (at level 200, x binder, right associativity,
        format "'[' 'Σ'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Section Construction.

    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model}. 

    Section incl_def.

    Definition im_incl (ρ ρ': nat -> M) := forall x, Σ y, ρ x = ρ' y.
    Definition im_incl_k (ρ ρ': nat -> M) k := forall x, x < k -> Σ y, ρ x = ρ' y.

    End incl_def.

    Notation "ρ ≼ ρ'" := (im_incl ρ ρ') (at level 25).
    Notation "ρ ≼[ k ] ρ'" := (im_incl_k ρ ρ' k) (at level 25).

    Section incl_prop.

    Lemma sat_incl ρ ρ': ρ ≼ ρ' -> forall φ, 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros H φ.
        exists (fun x => $ (projT1 (H x))).
        rewrite sat_comp; split.
        apply sat_ext.
        all: intro x; cbn; now destruct (H x).
    Qed.

    Lemma bounded_incl ρ ρ' φ k: bounded k φ -> ρ ≼[k] ρ' -> 
        exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ 
            (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
    Proof.
        intros.
        exists (fun x => match (lt_dec x k) with
                | left cp =>  $ (projT1 (H0 x cp)) 
                | right _ =>  $ x 
                end).
        rewrite sat_comp.
        split.
        apply bound_ext with k. exact H.
        intros; cbn.
        destruct (lt_dec n k); cbn.
        now destruct (H0 n l).
        congruence.
        intros x l; cbn.
        destruct (lt_dec x k); cbn.
        now destruct (H0 x l0).
        congruence.
    Qed.

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

    Definition wit_env (ρ ρ_s: env M) φ := exists w, M ⊨[ρ_s w .: ρ] φ -> M ⊨[ρ] (∀ φ).

    Lemma incl_impl_wit_env ρ ρ' ρ_s: ρ ≼ ρ' 
        -> (forall φ, wit_env ρ' ρ_s φ) -> (forall φ, wit_env ρ ρ_s φ).
    Proof.
        intros.
        destruct (sat_incl H (∀ φ)) as (σ & fH & EH).
        destruct (H0 (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply sat_ext'.
        destruct x; cbn. { easy. }
        rewrite <- EH.
        apply (cons_w ρ ρ' σ (ρ_s ws)).
    Qed.

    Lemma bounded_incl_impl_wit_env ρ ρ' ρ_s: (forall φ, wit_env ρ' ρ_s φ) 
        -> (forall φ k, bounded k φ -> ρ ≼[k] ρ' -> wit_env ρ ρ_s φ).
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (bounded_incl HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [ws P].
        exists ws.
        intro Hp; rewrite fH. 
        apply P; revert Hp.
        rewrite sat_comp.
        apply (bound_ext _ H); intros n Ln. 
        destruct n; cbn. {easy. }
        rewrite <- EH.
        - now rewrite (cons_w ρ ρ' σ (ρ_s ws)).
        - lia.
    Qed.  

    End incl_prop.

    Section incl_Path.

    Variable F: nat -> nat -> M.

    Hypothesis prop_F: forall n, (F n) ≼ (F (S n)).

    Lemma refl_incl: forall e, e ≼ e.
    Proof.
        intros n x.
        now exists x.
    Qed.

    Lemma trans_incl: forall a b c, a ≼ b -> b ≼ c -> a ≼ c.
    Proof.
        unfold "≼"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

    Lemma nil_F:
        forall n, F 0 ≼ F n.
    Proof.
        induction n. 
        - apply refl_incl.
        - eapply trans_incl.
          apply IHn.
          easy.
    Qed.

    Lemma mono_F' a b: F a ≼ F (a + b) .
    Proof.
        induction b.
        - assert (a + 0 = a) as -> by lia; apply refl_incl.
        - assert (a + S b = S(a + b)) as -> by lia.
          eapply trans_incl. exact IHb. exact (prop_F (a + b)).
    Qed.

    Lemma mono_F a b: a < b -> F a ≼ F b.
    Proof.
        assert (a < b -> Σ c, a + c = b) .
        intro H; exists (b - a); lia.
        intro aLb.
        destruct (H aLb) as [c Pc].
        specialize (mono_F' a c).
        now rewrite Pc. 
    Qed.

    End incl_Path.

    Section Fixed_point.

    Variable F: nat -> nat -> M.

    Definition wit_rel ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\ forall x, exists y, ρ x = ρ' y.

    Definition wit_rel_comp ρ ρ' :=
        (forall φ, wit_env ρ ρ' φ) /\ forall x, ρ x = ρ' (2 * x).

    Variable init_ρ: nat -> M.

    Hypothesis depandent_path:
        F 0 = init_ρ /\ forall n, wit_rel_comp (F n) (F (S n)).

    Lemma wit_rel_comp_implies_incl ρ ρ':
        wit_rel_comp ρ ρ' -> ρ ≼ ρ'.
    Proof.
        intros H x; exists (2 * x).
        now destruct H as [_ P].
    Qed.

    Lemma depandent_path_comp:
        forall n, F n ≼ F (S n) .
    Proof.
        destruct depandent_path as [_ H].
        now intro n; eapply wit_rel_comp_implies_incl.
    Qed.

    Opaque encode_p. 

    Definition fixed x := F (π__1 x) (π__2 x).

    Lemma union_incl n: (F n) ≼ fixed.
    Proof.
        intro x; exists (encode n x); cbn.
        unfold fixed.
        now rewrite cantor_left, cantor_right.
    Qed.

    Lemma union_fixed n: wit_rel (F n) fixed.
    Proof.
        split; intros.
        - unfold wit_env. 
          destruct depandent_path as [_ H].
          destruct (H n) as [H_ H_'].
          destruct (H_ φ) as [w H'].
          (* destruct (H'' w) as [w' Pw]. *)
          destruct (union_incl (S n) w) as [ws Pws].
          exists ws.
          intro; apply H'.
          now rewrite Pws.
        - exists (encode n x); cbn.
          unfold fixed.
          now rewrite cantor_left, cantor_right.
    Qed.

    (** Here we prove the principle of strong induction, induction on the natural
numbers where the inductive hypothesis includes all smaller natural numbers. *)


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


    Lemma bounded_rel b: 
        Σ E: nat, forall x, x < b -> Σ y, fixed x = F E y.
    Proof.
        intros.
        destruct (bounded_cantor b) as [E PE].
        exists E; intros.
        unfold fixed.
        specialize (PE _ H).
        specialize (mono_F depandent_path_comp PE) as H1.
        exists (projT1 (H1 (π__2 x))).
        now destruct (projT2 (H1 (π__2 x))).
    Qed.


    Theorem Fixed_point:
        wit_rel fixed fixed .
    Proof.
        split; intros.
        - destruct (find_bounded φ) as [b bφ].
          destruct (bounded_rel b) as [E P].
          (* enough (exists E: nat, forall x, x < b -> exists y, fixed x = F E y) as [E P]. *)
          unshelve eapply bounded_incl_impl_wit_env; [exact (F E) |exact b | |easy |..].
          + now destruct (union_fixed E) as [HB _].
          + intros x Lxb; apply (P x Lxb). 
        - now exists x.
    Qed.

    End Fixed_point.

    Section wit_rel_by_DC.

    Definition Even n := Σ m, n = 2 * m.
    Definition Odd n := Σ m, n = 2 * m + 1.
    Definition Even_Odd_dec n : Even n + Odd n.
    Proof.
        induction n as [|n [H1|H1]]; [left; exists 0; lia|..].
        - right; destruct H1 as [k H]; exists k; lia.
        - left; destruct H1 as [k H]; exists (S k); lia.
    Defined.

    Lemma not_Even_Odd_both n: 
         (Even n) * (Odd n) -> False.
    Proof.
        intros ([k Pk] &[t Pt]); lia.
    Qed.

    (* If the signature is countable *)
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    Definition FunctionalCountableChoice_on {A} :=
    forall (R:nat-> A->Prop),
        (forall n, exists y, R n y) ->
        (exists f : nat -> A, forall n, R n (f n)).

    Hypothesis DC: forall {A} R, total_rel R 
        -> forall w, exists F: nat -> A, F 0 = w /\ forall n, R (F n) (F (S n)).

    Notation FunctionalCountableChoice :=
        (forall A : Type, @FunctionalCountableChoice_on A).

    Theorem functional_countable_choice:
        FunctionalCountableChoice.
     Proof.
       intros A R H0.
       set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
       destruct (H0 0) as (y0,Hy0).
       destruct (@DC (nat*A)) with(R:=R') (w:=(0,y0)) as (f,(Hf0,HfS)).
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
           assumption.
     Qed.

    Definition AC_form: forall {B} (R: form -> B -> Prop), total_rel R 
        -> exists F: form -> B, forall x, R x (F x).
    Proof.
        intros.
        set (R' n := R (phi_ n)).
        assert (total_rel R') as H'. intro x.
        now destruct (H (phi_ x)) as [b Pb]; exists b.
        destruct (functional_countable_choice H') as [f Pf].
        exists (fun fm => f (nth_ fm)).
        intro x; specialize (Pf (nth_ x)).
        unfold R' in Pf.
        now rewrite (Hphi x) in Pf.
    Qed.

    Hypothesis drinker_paradox:
        forall {X} (P: X -> Prop),  inhabited X -> exists x, P x -> forall k, P k.

    Definition AC_app: 
        forall ρ, exists (W: nat -> M), forall φ, exists w, M ⊨[W w.:ρ] φ -> M ⊨[ρ] ∀ φ.
    Proof.
        intros.
        destruct (@AC_form M (fun phi w => M ⊨[w .: ρ] phi -> M ⊨[ρ] (∀ phi))) as [F PF].
        - intro φ; destruct (drinker_paradox (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
          constructor; exact (ρ O). exists w; intro Hx; cbn; now apply Hw.
        - exists (fun n: nat => F (phi_ n)).
          intro φ; specialize (PF φ).
          now exists (nth_ φ); rewrite (Hphi φ).
    Qed.

    Definition path root:
        exists F, F O = root /\ forall n, wit_rel_comp (F n) (F (S n)).
    Proof.
        unshelve eapply (DC  _ root).
        intro ρ; destruct (AC_app ρ) as [W P].
        unfold wit_rel_comp.
        exists (fun n => match Even_Odd_dec n with 
                | inl L => ρ (projT1 L)
                | inr R => W (projT1 R)
                end ); split.
        - intros phi; destruct (P phi) as [w Pw].
          exists (2 * w + 1). 
          assert (Odd (2 * w + 1)) by (exists w; lia).
          destruct (Even_Odd_dec (2 * w + 1)) eqn: E.
          now exfalso; apply (@not_Even_Odd_both (2*w + 1)).
          intro; apply Pw.
          specialize (projT2 o) as H'; cbn in H'.
          enough (pi1 o = w) as <- by easy.
          now enough ( (w + (w + 0)) + 1 = (pi1 o + (pi1 o + 0)) + 1) by lia.
        - intro x. destruct (Even_Odd_dec (2 * x)) eqn: E.
          destruct e; cbn; enough (x = x0) as -> by easy; nia.
          exfalso; eapply (@not_Even_Odd_both (2*x)); split; [now exists x| easy].  
    Qed.

    End wit_rel_by_DC.


End Construction.


Section Result.

    (* For any countable signature Σ *)
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Variable phi_ : nat -> form.
    Variable nth_ : form -> nat.
    Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

    (* with drinker paradox *)
    Hypothesis DP:
        forall {X} (P: X -> Prop), inhabited X -> exists x, P x -> forall k, P k.

    (* and the axiom of Denpendent choice *)
    Hypothesis DC:
        forall {X} (R : X -> X -> Prop), (total_rel R) 
            -> forall w, exists f : nat -> X, f O = w /\ forall n, R (f n) (f (S n)).

    (* For any model over Σ, there is an elementary submodel *)
    Theorem LS_downward: 
        forall (M: model) (root: env M), exists (N: model), N ⪳ M.
    Proof.
        intros.
        destruct (path Hphi (@DC) (@DP)) with (root := root) as [F PF].
        pose (depandent_path_comp PF) as Incl;
        pose (Fixed_point PF) as Fixed_point.
        apply Tarski_Vaught_Test' with (phi_ := phi_) (h := fixed F).
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        now destruct Fixed_point.
    Qed.

End Result.

