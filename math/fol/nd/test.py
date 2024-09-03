
import traceback
from nd import verify_plain, init_tables

Ok = 0
ErrSyntax = 1
ErrLogic = 2
ErrAssert = 3

def check(test_id, expected_result, code):
    init_tables()
    try:
        verify_plain(code)
        if not expected_result is Ok:
            print(f"Test {test_id} failed")
    except Exception as e:
        if expected_result is Ok:
            print(f"Test {test_id} failed")
            print("----")
            print(traceback.format_exc())
            return False
    return True

def main():
    for (test_id, result, code) in tests:
        if not check(test_id, result, code):
            break

tests = [
("1.0", Ok, ""),
("1.1", Ok, """
1. 1 |- A, basic.
2. |- A -> A, subj_intro 1.
"""),
("1.2", Ok, """
1. 1 |- A, basic.
2. 2 |- B, basic.
3. 1, 2 |- A /\ B, conj_intro 1 2.
"""),
("1.3", Ok, """
1. 1 |- A, basic.
2. 1 |- A \/ B, disj_introl 1.
"""),
("1.4", Ok, """
1. 1 |- B, basic.
2. 1 |- A \/ B, disj_intror 1.
"""),
("1.5", Ok, """
1. 1 |- false, basic.
2. |- ~false, neg_intro 1.
"""),
("1.6", Ok, """
1. 1 |- A -> B, basic.
2. 2 |- B -> A, basic.
3. 1, 2 |- A <-> B, bij_intro 1 2.
"""),
("1.7", Ok, """
1. 1 |- A /\ B, basic.
2. 1 |- A, conj_eliml 1.
"""),
("1.8", Ok, """
1. 1 |- A /\ B, basic.
2. 1 |- B, conj_elimr 1.
"""),
("1.9", Ok, """
1. 1 |- A -> B, basic.
2. 2 |- A, basic.
3. 1, 2 |- B, subj_elim 1 2.
"""),
("1.10", Ok, """
1. 1 |- ~A, basic.
2. 2 |- A, basic.
3. 1, 2 |- false, neg_elim 1 2.
4. 2 |- ~~A, neg_intro 3.
5. |- A -> ~~A, subj_intro 4.
"""),
("1.11", Ok, """
1. 1 |- (A -> B) /\ A, basic.
2. 1 |- A -> B, conj_eliml 1.
3. 1 |- A, conj_elimr 1.
4. 1 |- B, subj_elim 2 3.
5. |- (A -> B) /\ A -> B, subj_intro 4.
"""),
("1.12", Ok, """
1. 1 |- A /\ B, basic.
2. 1 |- A, conj_eliml 1.
3. 1 |- B, conj_elimr 1.
4. 1 |- B /\ A, conj_intro 3 2.
5. |- A /\ B -> B /\ A, subj_intro 4.
"""),
("1.13", Ok, """
1. 1 |- A \/ B, basic.
2. 2 |- A, basic.
3. 2 |- B \/ A, disj_intror 2.
4. 4 |- B, basic.
5. 4 |- B \/ A, disj_introl 4.
6. 1 |- B \/ A, disj_elim 1 3 5.
7. |- A \/ B -> B \/ A, subj_intro 6.
"""),
("1.14", Ok, """
1. 1 |- ~B, basic.
2. 2 |- A -> B, basic.
3. 3 |- A, basic.
4. 2, 3 |- B, subj_elim 2 3.
5. 1, 2, 3 |- false, neg_elim 1 4.
6. 1, 2 |- ~A, neg_intro 5.
7. 2 |- ~B -> ~A, subj_intro 6.
8. |- (A -> B) -> ~B -> ~A, subj_intro 7.
"""),
("1.15", Ok, """
DNE. |- ~~A -> A, axiom.
1. 1 |- ~A, basic.
2. 2 |- false, basic.
3. 1, 2 ⊢ false, basic.
4. 2 ⊢ ~~A, neg_intro 3.
5. 2 ⊢ A, subj_elim DNE 4.
6. ⊢ false -> A, subj_intro 5.
"""),
("1.16", Ok, """
DNE. |- ~~A -> A, axiom.
1. 1 |- ~(A \/ ~A), basic.
2. 2 |- A, basic.
3. 2 |- A ∨ ~A, disj_introl 2.
4. 1, 2 |- false, neg_elim 1 3.
5. 1 |- ~A, neg_intro 4.
6. 1 |- A \/ ~A, disj_intror 5.
7. 1 |- ⊥, neg_elim 1 6.
8. |- ~~(A \/ ~A), neg_intro 7.
9. |- ~~(A \/ ~A) -> A \/ ~A, subst DNE.
10. |- A \/ ~A, subj_elim 9 8.
"""),

("2.1", ErrLogic, """
1. 1 |- A, basic.
2. |- A -> A, subj_intro 1.
3. |- A -> B, subst 2.
"""),
("2.2", ErrLogic, """
1. 1 |- A, basic.
2. |- A -> A, subj_intro 1.
3. |- (A -> A) -> (A -> B), subst 2.
"""),

("3.1", Ok, """
1. 1 |- forall x. A x, basic.
2. 1 |- A u, uq_elim 1.
"""),
("3.2", Ok, """
1. 1 |- forall x. A x /\ B x, basic.
2. 1 |- A u /\ B u, uq_elim 1.
"""),
("3.3", Ok, """
1. 1 |- A u, basic.
2. 1 |- exists x. A x, ex_intro 1.
"""),
("3.4", Ok, """
1. 1 |- A x, basic.
2. |- A x -> A x, subj_intro 1.
3. |- forall x. A x -> A x, uq_intro 2.
"""),
("3.5", Ok, """
1. 1 |- A y, basic.
2. 1 |- exists x. A x, ex_intro 1.
3. |- A y -> exists x. A x, subj_intro 2.
4. |- forall y. A y -> exists x. A x, uq_intro 3.
"""),

("4.1", Ok, """
1. 1 |- P x, basic.
2. |- P x -> P x, subj_intro 1.
"""),
("4.2", ErrLogic, """
1. 1 |- P x, basic.
2. |- P x -> P y, subj_intro 1.
"""),
("4.3", Ok, """
1. |- P x A -> P x A, axiom.
2. |- x in A -> x in A, subst 1.
"""),
("4.4", Ok, """
1. |- P x -> P x, axiom.
2. |- P u -> P u, subst 1.
"""),
("4.5", ErrLogic, """
1. |- P x A -> P x A, axiom.
2. |- x in A -> x in B, subst 1.
"""),
("4.6", ErrLogic, """
1. |- P x A -> P x A, axiom.
2. |- x in A -> y in A, subst 1.
"""),
("4.7", Ok, """
1. |- P x A -> P x A, axiom.
2. |- y in B -> y in B, subst 1.
"""),

("5.1", Ok, """
1. |- forall x. P x, axiom.
2. |- forall x. P x, subst 1.
"""),
("5.2", Ok, """
1. |- forall x. P x, axiom.
2. |- forall y. P y, subst 1.
"""),
("5.3", Ok, """
1. |- forall x. P x, axiom.
2. |- forall y. Q y, subst 1.
"""),
("5.4", Ok, """
1. |- forall x. P x y, axiom.
2. |- forall u. P u v, subst 1.
"""),
("5.5", Ok, """
1. |- forall x. P x y, axiom.
2. |- forall x. x in A, subst 1.
"""),
("5.6", Ok, """
1. |- forall x. P x y, axiom.
2. |- forall y. P y y, subst 1.
"""), # It's fine, 1 is more general than 2.
("5.7", Ok, """
1. |- forall y. P y y, axiom.
2. |- forall x. Q x y, subst 1.
"""), # Also fine, this time because P is schematic.
("5.8", Ok, """
1. |- forall x. x in y, axiom.
2. |- forall y. y in y, subst 1.
"""), # Same argument as 5.6.
("5.9", ErrLogic, """
1. |- forall y. y in y, axiom.
2. |- forall x. x in y, subst 1.
"""), # This time it needs to fail.
("5.10", Ok, """
1. |- p x y <-> true, def.
2. |- forall x. p x y, axiom.
3. |- forall y. p y y, subst 2.
"""),
("5.11", ErrLogic, """
1. |- p x y <-> true, def.
2. |- forall y. p y y, axiom.
3. |- forall x. p x y, subst 2.
"""),
("5.12", Ok, """
1. |- P x, axiom.
2. |- Q x y, subst 1.
"""),
("5.12", ErrLogic, """
1. |- p x <-> true, def.
2. |- p x, axiom.
3. |- p x y, subst 2.
"""),

("6.1", Ok, """
1. |- forall x. P x /\ Q x, axiom.
2. |- P u /\ Q u, uq_elim 1.
"""),
("6.2", ErrLogic, """
1. |- forall x. P x /\ Q x, axiom.
2. |- P u /\ Q v, uq_elim 1.
"""),
("6.3", ErrLogic, """
1. |- p x <-> true, def.
2. |- q x <-> true, def.
3. |- forall x. p x /\ q x, axiom.
4. |- p u /\ p u, uq_elim 3.
"""),
("7.1", ErrLogic, """
1. |- A = {x | x = x}, def.
2. |- x in A, axiom.
3. |- x in B, subst 2.
"""),

("8.1", ErrLogic, """
1. |- A /\ x in A, axiom.
"""),
("8.2", ErrLogic, """
1. |- P x, axiom.
2. |- forall P. P x, uq_intro 1.
"""),
("8.3", ErrLogic, """
1. |- P x, axiom.
2. |- P (A /\ B), subst 1.
"""),
("8.4", ErrLogic, """
1. |- A, axiom.
2. |- forall A. A, uq_intro 1.
"""),
("8.5", ErrLogic, """
1. |- A /\ B, axiom.
2. |- forall A. A /\ B, uq_intro 1.
"""),
("8.6", Ok, """
1. |- forall x. P x y, axiom.
2. |- P u y, uq_elim 1.
"""),
("8.7", ErrLogic, """
1. |- forall x. P x y, axiom.
2. |- P u v, uq_elim 1.
"""),
("8.8", ErrLogic, """
1. |- A, subst 1.
""")
]

main()
