
import traceback
from nd import verify_plain, rules

Ok = 0
ErrSyntax = 1
ErrLogic = 2
ErrAssert = 3

def check(test_id, expected_result, code):
    book = {}
    verify_plain(book, rules)
    try:
        verify_plain(book, code)
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
("01.01", Ok, ""),
("01.02", Ok, """
1. 1 ⊢ A, basic.
2. ⊢ A → A, subj_intro 1.
"""),
("01.03", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. ⊢ A ∧ B → A ∧ B, subj_intro 1.
"""),
("01.04", Ok, """
1. 1 ⊢ A ∧ B ∧ C, basic.
2. ⊢ A ∧ B ∧ C → A ∧ B ∧ C, subj_intro 1.
"""),
("01.05", Ok, """
1. 1 ⊢ A ∧ B ∧ C ∧ D, basic.
2. ⊢ A ∧ B ∧ C ∧ D → A ∧ B ∧ C ∧ D, subj_intro 1.
"""),
("01.06", Ok, """
1. 1 ⊢ A → B, basic.
2. ⊢ (A → B) → A → B, subj_intro 1.
"""),
("01.07", Ok, """
1. 1 ⊢ A → B → C, basic.
2. ⊢ (A → B → C) → A → B → C, subj_intro 1.
"""),
("01.08", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
"""),
("01.09", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
"""),
("01.10", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 1, 2 ⊢ B ∧ A, conj_intro 2 1.
"""),
("01.11", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 3 ⊢ C, basic.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"""),
("01.12", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 3 ⊢ C, basic.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 2, 1 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"""),
("01.13", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 3 ⊢ C, basic.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 1, 2 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"""),
("01.14", Ok, """
1. 1 ⊢ A, basic.
2. 2 ⊢ B, basic.
3. 3 ⊢ C, basic.
4. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"""),
("01.15", Ok, """
1. 1 ⊢ A, basic.
2. 1 ⊢ A ∨ B, disj_introl 1.
"""),
("01.16", Ok, """
1. 1 ⊢ A, basic.
2. 1 ⊢ B ∨ A, disj_intror 1.
"""),
("01.17", Ok, """
1. 1 ⊢ A, basic.
2. 1 ⊢ A ∨ A, disj_introl 1.
"""),
("01.18", Ok, """
1. 1 ⊢ A, basic.
2. 1 ⊢ A ∨ A, disj_intror 1.
"""),
("01.19", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ A ∧ B ∨ C, disj_introl 1.
"""),
("01.20", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ C ∨ A ∧ B, disj_intror 1.
"""),
("01.21", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_introl 1.
"""),
("01.22", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_intror 1.
"""),
("01.23", Ok, """
1. 1 ⊢ ⊥, basic.
2. ⊢ ¬⊥, neg_intro 1.
"""),
("01.24", Ok, """
1. 1 ⊢ A → B, basic.
2. 2 ⊢ B → A, basic.
3. 1, 2 ⊢ A ↔ B, bij_intro 1 2.
"""),
("01.25", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ A, conj_eliml 1.
"""),
("01.26", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ B, conj_elimr 1.
"""),
("01.27", Ok, """
1. 1 ⊢ A ∧ B ∧ C, basic.
2. 1 ⊢ A ∧ B, conj_eliml 1.
"""),
("01.28", Ok, """
1. 1 ⊢ A ∧ B ∧ C, basic.
2. 1 ⊢ C, conj_elimr 1.
"""),
("01.29", Ok, """
1. 1 ⊢ A → B, basic.
2. 2 ⊢ A, basic.
3. 1, 2 ⊢ B, subj_elim 1 2.
"""),
("01.30", Ok, """
1. 1 ⊢ A ∧ B → C ∧ D, basic.
2. 2 ⊢ A ∧ B, basic.
3. 1, 2 ⊢ C ∧ D, subj_elim 1 2.
"""),
("01.31", Ok, """
1. 1 ⊢ A → B → C, basic.
2. 2 ⊢ A, basic.
3. 1, 2 ⊢ B → C, subj_elim 1 2.
4. 4 ⊢ B, basic.
5. 1, 2, 4 ⊢ C, subj_elim 3 4.
6. 4, 2, 1 ⊢ C, subj_elim 3 4.
"""),
("01.32", Ok, """
1. 1 ⊢ A ↔ B, basic.
2. 1 ⊢ A → B, bij_eliml 1.
"""),
("01.33", Ok, """
1. 1 ⊢ A ↔ B, basic.
2. 1 ⊢ B → A, bij_elimr 1.
"""),
("01.34", Ok, """
1. 1 ⊢ ¬A, basic.
2. 2 ⊢ A, basic.
3. 2, 1 ⊢ ⊥, neg_elim 1 2.
4. 2 ⊢ ¬¬A, neg_intro 3.
5. ⊢ A → ¬¬A, subj_intro 4.
"""),
("01.35", Ok, """
1. 1 ⊢ (A → B) ∧ A, basic.
2. 1 ⊢ A → B, conj_eliml 1.
3. 1 ⊢ A, conj_elimr 1.
4. 1 ⊢ B, subj_elim 2 3.
5. ⊢ (A → B) ∧ A → B, subj_intro 4.
"""),
("01.36", Ok, """
1. 1 ⊢ A ∧ B, basic.
2. 1 ⊢ A, conj_eliml 1.
3. 1 ⊢ B, conj_elimr 1.
4. 1 ⊢ B ∧ A, conj_intro 3 2.
5. ⊢ A ∧ B → B ∧ A, subj_intro 4.
"""),
("01.37", Ok, """
1. 1 ⊢ A ∨ B, basic.
2. 2 ⊢ A, basic.
3. 2 ⊢ B ∨ A, disj_intror 2.
4. 4 ⊢ B, basic.
5. 4 ⊢ B ∨ A, disj_introl 4.
6. 1 ⊢ B ∨ A, disj_elim 1 3 5.
7. ⊢ A ∨ B → B ∨ A, subj_intro 6.
"""),
("01.38", Ok, """
1. 1 ⊢ ¬B, basic.
2. 2 ⊢ A → B, basic.
3. 3 ⊢ A, basic.
4. 2, 3 ⊢ B, subj_elim 2 3.
5. 2, 1, 3 ⊢ ⊥, neg_elim 1 4.
6. 2, 1 ⊢ ¬A, neg_intro 5.
7. 2 ⊢ ¬B → ¬A, subj_intro 6.
8. ⊢ (A → B) → ¬B → ¬A, subj_intro 7.
"""),

("02.01", ErrLogic, """
1. 1 ⊢ A, basic.
2. ⊢ B → A, subj_intro 1.
"""),
("02.02", ErrLogic, """
1. 1 ⊢ A, basic.
2. ⊢ A → B, subj_intro 1.
"""),
("02.03", ErrLogic, """
1. 1 ⊢ A ∧ B, basic.
2. ⊢ A ∧ A → A ∧ A, subj_intro 1.
"""),

("03.01", Ok, """
1. 1 ⊢ ∀x. A x, basic.
2. 1 ⊢ A u, uq_elim 1.
"""),
("03.02", Ok, """
1. 1 ⊢ ∀x. A x, basic.
2. 1 ⊢ A w, uq_elim 1.
"""),
("03.03", Ok, """
1. 1 ⊢ ∀x. A x, basic.
2. 1 ⊢ A x, uq_elim 1.
"""),
("03.04", Ok, """
1. 1 ⊢ ∀x. A x ∧ B x, basic.
2. 1 ⊢ A u ∧ B u, uq_elim 1.
"""),
("03.05", Ok, """
1. 1 ⊢ A u, basic.
2. ⊢ A u → A u, subj_intro 1.
3. ⊢ ∀x. A x → A x, uq_intro u 2.
"""),

("04.01", ErrLogic, """
1. 1 ⊢ ∀x. A x, basic.
2. 1 ⊢ B u, uq_elim 1.
"""),
("04.02", ErrLogic, """
1. 1 ⊢ ∀x. A x ∧ B x, basic.
2. 1 ⊢ A u ∧ A u, uq_elim 1.
"""),
("04.03", ErrLogic, """
1. 1 ⊢ ∀x. A x ∧ B x, basic.
2. 1 ⊢ A u ∧ B w, uq_elim 1.
"""),
("04.04", ErrLogic, """
1. 1 ⊢ A u, basic.
2. 1 ⊢ ∀x. A x, uq_intro u 1.
""")
]

main()
