Require Import ZArith Arith List syntax little Lia.

Import ListNotations.

Module compiler (S : little_syntax).

Import S.

Inductive assembly :=
  push (n : Z) |
  pop |
  add |
  cmp |
  load (n : nat) |
   store (n : nat) | goto (n : nat) | branch (n : nat).

Definition asm_step_new_stack (stack mem : list Z) (i : assembly) :
  list Z :=
  match i with
  | push v => v :: stack
  | pop => tl stack
  | add => match stack with a :: b :: s => (a + b)%Z :: s | _ => nil end
  | cmp =>
    match stack with a :: b :: s => Z.b2z(a <=? b)%Z :: s | _ => nil end
  | load n => nth n mem 0%Z :: stack
  | store n => tl stack
  | goto n => stack
  | branch n => tl stack
  end.

Definition asm_step_new_pc (stack mem : list Z) (i : assembly) (pc : nat) :
  nat :=
  match i with
  | push n => pc + 1
  | pop => pc + 1
  | add => pc + 1
  | cmp => pc + 1
  | load n => pc + 1
  | store n => pc + 1
  | goto n => n
  | branch n => 
    if (hd 0 stack =? Z.b2z true)%Z then n else pc + 1
  end.

Fixpoint set_nth (l : list Z)(i : nat)(v : Z) :=
  match l, i with
  | x :: m, 0%nat => v :: m
  | x :: m, S i' => x :: set_nth m i' v
  | _, _ => nil
  end.

Definition asm_step_new_mem (stack mem : list Z) (i : assembly) :
  list Z :=
  match i with
  | push n => mem
  | pop => mem
  | add => mem
  | cmp => mem
  | load n => mem
  | store n => 
    match stack with
    | v :: s => set_nth mem n v
    | _ => nil
    end
  | goto n => mem
  | branch n => mem
  end.

Fixpoint exec_asm 
   (exec_count : nat)(pg : list assembly)(stack mem : list Z) (pc : nat) 
   :=
  match exec_count with
  | 0%nat => (stack, mem, pc)
  | S ec =>
    match nth_error pg pc with
    | None => (stack, mem, pc)
    | Some i =>
      exec_asm ec pg (asm_step_new_stack stack mem i)
             (asm_step_new_mem stack mem i)
             (asm_step_new_pc stack mem i pc)
    end
  end.

Fixpoint env_to_mem (l : list (string * Z)) : list Z :=
  match l with (s, v) :: l' => v :: env_to_mem l' | nil => nil end.

Fixpoint symbol_index (l : list (string * Z))(s : string) : nat :=
  match l with
  | nil => 0
  | (s', _) :: l' =>
    if string_dec s s' then 0 else S (symbol_index l' s)
  end.

Fixpoint compile_aexp (env : list (string * Z))
  (e : aexpr0 string) : list assembly :=
  match e with
  | avar s => [load (symbol_index env s)]
  | anum n => [push n]
  | aplus e1 e2 =>
    compile_aexp env e1 ++ compile_aexp env e2 ++ [add]
  end.

Definition compile_bexp (env : list (string * Z))
  (b : bexpr0 string) : list assembly :=
  match b with
  | blt e1 e2 => 
    compile_aexp env e1 ++ compile_aexp env e2 ++ [cmp]
  end.

Fixpoint compile_instr (env : list (string * Z))(loc : nat)
  (i : instr0 string) {struct i} : list assembly :=
match i with
| assign s e =>
  let cp_exp := compile_aexp env e in
  compile_aexp env e ++ [store (symbol_index env s)]
| sequence i1 i2 =>
  let pg1 := compile_instr env loc i1 in
  let pg2 := compile_instr env (loc + length pg1) i2 in
  pg1 ++ pg2
| while b i1 =>
  let pge := compile_bexp env b in
  let pgi := compile_instr env (loc + length pge + 1) i1 in
  pge ++ branch (loc + length pge + length pgi + 2) ::
  pgi ++ [goto loc]
| skip => []
end. 

End compiler.

Module compiler_proofs (S : little_syntax).

Module comp := compiler S.
Module dyn := little S.

Import comp.
Import dyn.

Lemma exec_avar : forall n env e v pg1 pg2 stk,
  aeval env e v -> e = avar n ->
   exec_asm 1 (pg1 ++ compile_aexp env e ++ pg2) stk (env_to_mem env)
   (length pg1) =
   (v :: stk, env_to_mem env, (length pg1 + 1)%nat).
Proof.
intros n env e v pg1 pg2 stk dyn.
induction dyn as [r v | r x v | r x y v v' xny dyn Ih |
   r e1 e2 v1 v2 dyn1 Ih1 dyn2 Ih2].
      discriminate.
    intros [= xn]; simpl.
    destruct (S.string_dec x x) as [ _ | abs];[simpl | now case abs].
    now rewrite nth_error_app2, Nat.sub_diag; simpl.
  intros [= xn]; simpl.
  destruct (S.string_dec x y) as [ abs | _];[now case xny | simpl].
  rewrite nth_error_app2, Nat.sub_diag; simpl; auto with arith.
  revert Ih; rewrite xn; simpl.
  rewrite nth_error_app2, Nat.sub_diag; simpl; auto with arith.
  intros Ih; assert (Ih' := Ih eq_refl); injection Ih'.
  now intros v'q; rewrite v'q.
discriminate.
Qed.

Lemma exec_asm_seq :
  forall pg stk stk1 mem mem1 ec1 ec2 pc pc1,
  exec_asm ec1 pg stk mem pc = (stk1, mem1, pc1) ->
  exec_asm (ec1 + ec2) pg stk mem pc =
  exec_asm ec2 pg stk1 mem1 pc1.
Proof.
intros pg stk stk1 mem mem1 ec1; revert stk stk1 mem mem1.
induction ec1.
  simpl; intros stk stk1 mem mem1 ec2 pc pc1 [= stst mm pp].
  now subst.
intros stk stk1 mem mem1 ec2 pc pc1.
  simpl.
destruct (nth_error pg pc) as [i | ] eqn:nthq; cycle 1.
  intros [= -> -> ->].
  case ec2 as [ | ec].
    auto.
  now simpl; rewrite nthq.
intros cnd1.
now apply IHec1.
Qed.

Lemma exec_aexp :
  forall env e v pg1 pg2 stk,
  aeval env e v ->
  exists ec, 
  exec_asm ec (pg1 ++ compile_aexp env e ++ pg2)
       stk (env_to_mem env) (length pg1) =
  (v :: stk, env_to_mem env,
   (length pg1 + length (compile_aexp env e))%nat).
Proof.
intros env e v pg1 pg2 stk dyn; revert pg1 pg2 stk.
induction dyn as [r n | r x v | r x y v v' xny dyn Ih| 
                  r e1 e2 v1 v2 dyn1 Ih1 dyn2 Ih2].
      intros pg1 pg2 stk; exists 1%nat; simpl.
      now rewrite nth_error_app2, Nat.sub_diag; simpl.
    intros pg1 pg2 stk; exists 1%nat.
    apply (exec_avar x).
      constructor.
    easy.
  intros pg1 pg2 stk; exists 1%nat.
  apply (exec_avar x).
    now constructor.
  easy.
intros pg1 pg2 stk.
destruct (Ih1 pg1 (compile_aexp r e2 ++ [add] ++ pg2) stk) as [ec1 Pec1].
destruct (Ih2 (pg1 ++ (compile_aexp r e1)) (add :: pg2) (v1 :: stk)) as
   [ec2 Pec2].
exists (ec1 + ec2 + 1)%nat.
simpl.
revert Pec1 Pec2; rewrite <-!app_assoc; simpl.
rewrite app_length.
set (pg := pg1 ++ _); intros Pec1 Pec2.
assert 
  (both_exp : exec_asm (ec1 + ec2) pg stk (env_to_mem r) (length pg1) =
    (v2 :: v1 :: stk, env_to_mem r, 
    (length pg1 + length (compile_aexp r e1) +
     length (compile_aexp r e2)))%nat).
  rewrite (exec_asm_seq pg _ (v1 :: stk) _ (env_to_mem r)
    _ _ _ (length pg1 + length (compile_aexp r e1))%nat Pec1).
  easy.
rewrite app_length.
rewrite (exec_asm_seq _ _ (v2 :: v1 :: stk) _ (env_to_mem r)
            _ _ _ _ both_exp).
unfold pg; simpl.
rewrite 2!app_assoc.
rewrite nth_error_app2;[ | now rewrite !app_length; auto with arith].
rewrite !app_length, Nat.sub_diag; simpl.
now rewrite (Z.add_comm v2 v1), !Nat.add_assoc.
Qed.

Lemma exec_bexp :
  forall env e1 e2 v pg1 pg2 stk,
  beval env (blt e1 e2) v ->
  exists ec, 
  exec_asm ec (pg1 ++ compile_bexp env (blt e1 e2) ++ pg2)
       stk (env_to_mem env) (length pg1) =
  (Z.b2z (negb v) :: stk, env_to_mem env, 
   (length pg1 + length (compile_bexp env (blt e1 e2)))%nat).
Proof.
intros env e1 e2 v pg1 pg2 stk dyn.
inversion dyn as [r e1' e2' v1 v2 ev1 ev2 cmp1| 
                  r e1' e2' v1 v2 ev1 ev2 cmp2].
  destruct (exec_aexp env e1 v1 pg1 (compile_aexp env e2 ++ [cmp] ++ pg2)
                    stk ev1) as [ec1 Pec1].
  destruct (exec_aexp env e2 v2 (pg1 ++ compile_aexp env e1) ([cmp] ++ pg2)
              (v1 :: stk) ev2) as [ec2 Pec2].
  revert Pec1 Pec2; simpl; rewrite <-!app_assoc; simpl; set (pg := pg1 ++ _).
  rewrite app_length.
  intros Pec1 Pec2; exists (ec1 + ec2 + 1)%nat.
  assert 
    (both_exp : exec_asm (ec1 + ec2) pg stk (env_to_mem env) (length pg1) =
    (v2 :: v1 :: stk, env_to_mem env, 
    (length pg1 + length (compile_aexp env e1) +
     length (compile_aexp env e2)))%nat).
    rewrite (exec_asm_seq pg _ (v1 :: stk) _ (env_to_mem env)
      _ _ _ (length pg1 + length (compile_aexp env e1))%nat Pec1).
    easy.
  rewrite (exec_asm_seq _ _ (v2 :: v1 :: stk) _ (env_to_mem env)
            _ _ _ _ both_exp).
  unfold pg; simpl.
  rewrite 2!app_assoc.
  rewrite nth_error_app2;[ | now rewrite !app_length; auto with arith].
  rewrite !app_length, Nat.sub_diag; simpl.
  assert (cmpv : v2 <=? v1 = false) by now rewrite Z.leb_gt.
  now rewrite cmpv, !Nat.add_assoc.

destruct (exec_aexp env e1 v1 pg1 (compile_aexp env e2 ++ [cmp] ++ pg2)
                    stk ev1) as [ec1 Pec1].
destruct (exec_aexp env e2 v2 (pg1 ++ compile_aexp env e1) ([cmp] ++ pg2)
              (v1 :: stk) ev2) as [ec2 Pec2].
revert Pec1 Pec2; simpl; rewrite <-!app_assoc; simpl; set (pg := pg1 ++ _).
rewrite app_length.
intros Pec1 Pec2; exists (ec1 + ec2 + 1)%nat.
assert 
    (both_exp : exec_asm (ec1 + ec2) pg stk (env_to_mem env) (length pg1) =
    (v2 :: v1 :: stk, env_to_mem env, 
    (length pg1 + length (compile_aexp env e1) +
     length (compile_aexp env e2)))%nat).
  rewrite (exec_asm_seq pg _ (v1 :: stk) _ (env_to_mem env)
      _ _ _ (length pg1 + length (compile_aexp env e1))%nat Pec1).
  easy.
rewrite (exec_asm_seq _ _ (v2 :: v1 :: stk) _ (env_to_mem env)
            _ _ _ _ both_exp).
unfold pg; simpl.
rewrite 2!app_assoc.
rewrite nth_error_app2;[ | now rewrite !app_length; auto with arith].
rewrite !app_length, Nat.sub_diag; simpl.
assert (cmpv : v2 <=? v1 = true) by now rewrite Z.leb_le.
now rewrite cmpv, !Nat.add_assoc.
Qed.

Lemma update_set_nth : forall r x v r', 
  s_update r x v r' ->
  set_nth (env_to_mem r) (symbol_index r x) v = (env_to_mem r').
Proof.
induction 1 as [env x v v' | env env' x y v v' upd Ih xny].
  simpl.
  now destruct (S.string_dec x x) as [_ | abs];[ | now case abs].
simpl.
destruct (S.string_dec x y) as [abs | _];[ now case xny |].
now rewrite Ih.
Qed.

Lemma update_index r x v r' z :
  s_update r x v r' ->
  symbol_index r z = symbol_index r' z.
Proof.
induction 1 as [r x v v' | r r' x y v v' up Ih xny].
  easy.
now simpl; rewrite Ih.
Qed.

Lemma update_compile_aexp r x v r' e :
  s_update r x v r' ->
  compile_aexp r e = compile_aexp r' e.
Proof.
intros up; induction e as [n | y | e1 Ih1 e2 Ih2].
    now simpl; rewrite (update_index _ _ _ _ _ up).
  easy.
now simpl; rewrite Ih1, Ih2.
Qed.

Lemma update_compile_bexp r x v r' e :
  s_update r x v r' ->
  compile_bexp r e = compile_bexp r' e.
Proof.
intros up; induction e as [e1 e2].
now simpl; rewrite !(update_compile_aexp _ _ _ _ _ up).
Qed.

Lemma update_compile_instr r x v r' i n :
  s_update r x v r' ->
  compile_instr r n i = compile_instr r' n i.
Proof.
intros up; revert n; induction i as [y e | i1 Ih1 i2 Ih2| b i Ih| ].
      now intros n; simpl; rewrite (update_index _ _ _ _ _ up),
        (update_compile_aexp _ _ _ _ _ up).
    intros n; simpl.
    now rewrite Ih1, Ih2.
  intros n; simpl; rewrite (update_compile_bexp _ _ _ _ _ up).
  now rewrite Ih.
easy.
Qed.

Lemma exec_compile_aexp r i1 r' a :
  exec r i1 r' -> compile_aexp r a = compile_aexp r' a.
Proof.
induction 1 as [ r | r r' s e v ev up| r r' r'' i1_1 i1_2 ex1 Ih1 ex2 Ih2 |
                     r r' r'' b i ev ex1 Ih1 ex2 Ih2|  ]; try easy.
    now apply (update_compile_aexp _ _ _ _ _ up).
  now rewrite <- Ih2.
now rewrite <- Ih2.
Qed.

Lemma exec_compile_instr r i1 r' i2 n :
  exec r i1 r' ->
  compile_instr r n i2 = compile_instr r' n i2.
Proof.
induction 1 as [ r | r r' s e v ev up| r r' r'' i1_1 i1_2 ex1 Ih1 ex2 Ih2 |
                     r r' r'' b i ev ex1 Ih1 ex2 Ih2|  ].
        easy.
      now apply (update_compile_instr _ _ _ _ _ _ up).
    now rewrite <- Ih2.
  now rewrite <- Ih2.
easy.
Qed.

Lemma compile_instr_complete :
  forall env env' i pg1 pg2 stk,
  exec env i env' ->
  exists ec, 
  exec_asm ec (pg1 ++ compile_instr env (length pg1) i ++ pg2)
       stk (env_to_mem env) (length pg1) =
  (stk, env_to_mem env', 
   (length pg1 + length (compile_instr env (length pg1) i))%nat).
Proof.
intros env env' i pg1 pg2 stk dyn; revert pg1 pg2 stk.
induction dyn as [ | env env' x e v ev up |
   env env' env'' i1 i2 dyn1 Ih1 dyn2 Ih2|
   env env' env''  [e1 e2] i ev dyn1 Ih1 dyn2 Ih2 | env [e1 e2] i ev ].
        intros pg1 pg2 stk.
        now exists 0%nat; simpl; rewrite Nat.add_0_r.
      intros pg1 pg2 stk.
      destruct 
         (exec_aexp env e v pg1 (store (symbol_index env x) :: pg2) stk) as
        [ec Pec]; auto.
      exists (ec + 1)%nat.
      simpl; rewrite <-!app_assoc; simpl; set (pg := pg1 ++ _).
      fold pg in Pec.
      assert (t1 := exec_asm_seq pg _ _ _ _ _ 1 _ _ Pec).
      rewrite t1; unfold pg; simpl; rewrite nth_error_app2; [ | lia].
      rewrite minus_plus, <- (Nat.add_0_r (length _)).
      rewrite nth_error_app2;[ | lia].
      rewrite minus_plus; simpl.
      assert (t2 := update_set_nth _ _ _ _ up).
      now rewrite t2, app_length, Nat.add_0_r, Nat.add_assoc.
    intros pg1 pg2 stk.
    destruct (Ih1 pg1
               (compile_instr env
                  (length pg1 + length (compile_instr env (length pg1) i1))
                   i2 ++ pg2) stk) as [ec1 Pec1].
    revert Pec1; set (pg := (pg1 ++ _)); intros Pec1.
    destruct (Ih2 (pg1 ++ (compile_instr env (length pg1) i1)) pg2 stk)
        as [ec2 Pec2].
    revert Pec2; rewrite <-!app_assoc, app_length.
    rewrite <-! (exec_compile_instr _ _ _ _ _ dyn1); fold pg; intros Pec2.
    simpl; rewrite <-!app_assoc, !app_length; fold pg.
    exists (ec1 + ec2)%nat.
    assert (t1 := exec_asm_seq pg _ _ _ _ _ ec2 _ _ Pec1).
    now rewrite t1, Pec2; rewrite !Nat.add_assoc.
  intros pg1 pg2 stk.
  cbn [compile_instr compile_bexp].
  rewrite !app_length, !Nat.add_assoc, <-! app_assoc.
  repeat simpl (length [_]).
  set (middle_pc := (_ + 1 + 1)%nat).
  set (last_pc := (_ + 2)%nat).
  change (branch last_pc :: compile_instr env middle_pc i ++ [goto (length pg1)])
     with
   ([branch last_pc] ++ compile_instr env middle_pc i ++ [goto (length pg1)]).
  rewrite <-!app_assoc.
  set (pg := pg1 ++ _).
  destruct (exec_bexp _ _ _ _ pg1
              ([branch last_pc] ++
               compile_instr env (length pg1 +
                 length (compile_bexp env (blt e1 e2)) + 1) i
                ++ [goto (length pg1)] ++ pg2) stk ev) as [ec1 Pec1].
  revert Pec1; cbn [compile_instr compile_bexp].
  rewrite !app_length, !Nat.add_assoc, <- !app_assoc.
  simpl (length [ _ ]); fold middle_pc; fold pg; intros Pec1.
  destruct (Ih1 (pg1 ++ compile_bexp env (blt e1 e2) ++ [branch last_pc])
              ([goto (length pg1)] ++ pg2) stk) as [ec2 Pec2].
  revert Pec2; cbn [compile_instr compile_bexp].
  rewrite !app_length, !Nat.add_assoc, <- !app_assoc.
  simpl (length [cmp]); simpl (length [branch _]).
  fold middle_pc; fold pg; intros Pec2.
  destruct (Ih2 pg1 pg2 stk) as [ec3 Pec3].
  revert Pec3; cbn [compile_instr compile_bexp].
  rewrite !app_length, !Nat.add_assoc, <- !app_assoc.
  simpl (length [cmp]); simpl (length [branch _]).
  rewrite <-! (exec_compile_aexp _ _ _ _ dyn1).
  rewrite <-! (exec_compile_instr _ _ _ _ _ dyn1).
  fold middle_pc; fold last_pc.
  change (branch last_pc :: compile_instr env middle_pc i ++
          [goto (length pg1)]) with
     ([branch last_pc] ++ compile_instr env middle_pc i ++ [goto (length pg1)]).
  rewrite <- !app_assoc; fold pg; intros Pec3.
  exists (ec1 + (1 + (ec2 + (1 + ec3))))%nat.
  rewrite (exec_asm_seq pg _ (Z.b2z (negb true) :: stk) _ _ _ _ _ _ Pec1).
  rewrite (exec_asm_seq pg (Z.b2z (negb true) :: stk) stk (env_to_mem env)
             (env_to_mem env) 1 (ec2 + (1 + ec3))
             (length pg1 + length (compile_aexp env e1) +
                  length (compile_aexp env e2) + 1) middle_pc); cycle 1.
    simpl; unfold pg; rewrite <-!Nat.add_assoc.
    repeat (rewrite nth_error_app2, minus_plus; [ | lia]).
    now simpl; rewrite !Nat.add_assoc.
  rewrite (exec_asm_seq pg _ stk _ _ _ _ _ _ Pec2).
  rewrite (exec_asm_seq pg stk stk (env_to_mem env')
             (env_to_mem env') 1 ec3 _ (length pg1)); cycle 1.
    simpl; unfold pg, middle_pc; rewrite <-!Nat.add_assoc.
    repeat (rewrite nth_error_app2, minus_plus; [ | lia]).
    simpl.
    repeat (rewrite nth_error_app2, minus_plus; [ | lia]).
    simpl.
    set (L := length (compile_instr _ _ _)); rewrite <- (Nat.add_0_r L).
    unfold L.
    repeat (rewrite nth_error_app2, minus_plus; [ | lia]).
    easy.
  rewrite Pec3; unfold middle_pc; rewrite !app_length; simpl (length [_]).
  now rewrite !Nat.add_assoc.
intros pg1 pg2 stk.
cbn [compile_instr compile_bexp].
rewrite !app_length, !Nat.add_assoc, <-! app_assoc.
repeat simpl (length [_]).
set (middle_pc := (_ + 1 + 1)%nat).
set (last_pc := (_ + 2)%nat).
change (branch last_pc :: compile_instr env middle_pc i ++ [goto (length pg1)])
    with
 ([branch last_pc] ++ compile_instr env middle_pc i ++ [goto (length pg1)]).
rewrite <-!app_assoc.
set (pg := pg1 ++ _).
destruct (exec_bexp _ _ _ _ pg1
            ([branch last_pc] ++
             compile_instr env (length pg1 +
               length (compile_bexp env (blt e1 e2)) + 1) i
              ++ [goto (length pg1)] ++ pg2) stk ev) as [ec1 Pec1].
revert Pec1; cbn [compile_instr compile_bexp].
rewrite !app_length, !Nat.add_assoc, <- !app_assoc.
simpl (length [ _ ]); fold middle_pc; fold pg; intros Pec1.
exists (ec1 + 1)%nat.
rewrite (exec_asm_seq _ _ (Z.b2z (negb false) :: stk) _ _ _ 1 _ _ Pec1).
simpl.
unfold pg; rewrite <-!Nat.add_assoc.
repeat (rewrite nth_error_app2, minus_plus; [ | lia]).
simpl.
unfold last_pc, middle_pc.
apply f_equal; lia.
Qed.

End compiler_proofs.
