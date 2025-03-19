
use crate::{Env, verify, ErrorKind, load_prelude};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Expected {Ok, ErrLogic, ErrSyntax}

const OK: Expected = Expected::Ok;
const ELOGIC: Expected = Expected::ErrLogic;
const ESYNTAX: Expected = Expected::ErrSyntax;

#[test]
fn run_test_list() {
    let mut env = Env::new();
    for (test_id, expected, code) in TESTS {
        env.book.clear();
        load_prelude(&mut env);
        let result = match verify(&mut env, code.as_bytes()) {
            Ok(()) => OK,
            Err(e) => match e.kind {
                ErrorKind::Logic => ELOGIC,
                ErrorKind::Syntax => ESYNTAX
            }
        };
        assert!(result == *expected, "Test {} failed.", test_id);
    }
}

static TESTS: &[(&str, Expected, &str)] = &[
("01.01", OK, ""),
("01.02", OK, "
1. 1 ⊢ A, hypo.
2. ⊢ A → A, subj_intro 1.
"),
("01.03", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. ⊢ A ∧ B → A ∧ B, subj_intro 1.
"),
("01.04", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. ⊢ A ∧ B ∧ C → A ∧ B ∧ C, subj_intro 1.
"),
("01.05", OK, "
1. 1 ⊢ A ∧ B ∧ C ∧ D, hypo.
2. ⊢ A ∧ B ∧ C ∧ D → A ∧ B ∧ C ∧ D, subj_intro 1.
"),
("01.06", OK, "
1. 1 ⊢ A → B, hypo.
2. ⊢ (A → B) → A → B, subj_intro 1.
"),
("01.07", OK, "
1. 1 ⊢ A → B → C, hypo.
2. ⊢ (A → B → C) → A → B → C, subj_intro 1.
"),
("01.08", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
"),
("01.09", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
"),
("01.10", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 1, 2 ⊢ B ∧ A, conj_intro 2 1.
"),
("01.11", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"),
("01.12", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 2, 1 ⊢ A ∧ B ∧ C, conj_intro 4 3.
"),
("01.13", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 1, 2 ⊢ A ∧ B, conj_intro 1 2.
5. 3, 1, 2 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"),
("01.14", OK, "
1. 1 ⊢ A, hypo.
2. 2 ⊢ B, hypo.
3. 3 ⊢ C, hypo.
4. 2, 1 ⊢ A ∧ B, conj_intro 1 2.
5. 1, 2, 3 ⊢ C ∧ (A ∧ B), conj_intro 3 4.
"),
("01.15", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ B, disj_introl 1.
"),
("01.16", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ B ∨ A, disj_intror 1.
"),
("01.17", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ A, disj_introl 1.
"),
("01.18", OK, "
1. 1 ⊢ A, hypo.
2. 1 ⊢ A ∨ A, disj_intror 1.
"),
("01.19", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ C, disj_introl 1.
"),
("01.20", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ C ∨ A ∧ B, disj_intror 1.
"),
("01.21", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_introl 1.
"),
("01.22", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A ∧ B ∨ A ∧ B, disj_intror 1.
"),
("01.23", OK, "
1. 1 ⊢ ⊥, hypo.
2. ⊢ ¬⊥, neg_intro 1.
"),
("01.24", OK, "
1. 1 ⊢ A → B, hypo.
2. 2 ⊢ B → A, hypo.
3. 1, 2 ⊢ A ↔ B, bij_intro 1 2.
"),
("01.25", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A, conj_eliml 1.
"),
("01.26", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ B, conj_elimr 1.
"),
("01.27", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. 1 ⊢ A ∧ B, conj_eliml 1.
"),
("01.28", OK, "
1. 1 ⊢ A ∧ B ∧ C, hypo.
2. 1 ⊢ C, conj_elimr 1.
"),
("01.29", OK, "
1. 1 ⊢ A → B, hypo.
2. 2 ⊢ A, hypo.
3. 1, 2 ⊢ B, subj_elim 1 2.
"),
("01.30", OK, "
1. 1 ⊢ A ∧ B → C ∧ D, hypo.
2. 2 ⊢ A ∧ B, hypo.
3. 1, 2 ⊢ C ∧ D, subj_elim 1 2.
"),
("01.31", OK, "
1. 1 ⊢ A → B → C, hypo.
2. 2 ⊢ A, hypo.
3. 1, 2 ⊢ B → C, subj_elim 1 2.
4. 4 ⊢ B, hypo.
5. 1, 2, 4 ⊢ C, subj_elim 3 4.
6. 4, 2, 1 ⊢ C, subj_elim 3 4.
"),
("01.32", OK, "
1. 1 ⊢ A ↔ B, hypo.
2. 1 ⊢ A → B, bij_eliml 1.
"),
("01.33", OK, "
1. 1 ⊢ A ↔ B, hypo.
2. 1 ⊢ B → A, bij_elimr 1.
"),
("01.34", OK, "
1. 1 ⊢ ¬A, hypo.
2. 2 ⊢ A, hypo.
3. 2, 1 ⊢ ⊥, neg_elim 1 2.
4. 2 ⊢ ¬¬A, neg_intro 3.
5. ⊢ A → ¬¬A, subj_intro 4.
"),
("01.35", OK, "
1. 1 ⊢ (A → B) ∧ A, hypo.
2. 1 ⊢ A → B, conj_eliml 1.
3. 1 ⊢ A, conj_elimr 1.
4. 1 ⊢ B, subj_elim 2 3.
5. ⊢ (A → B) ∧ A → B, subj_intro 4.
"),
("01.36", OK, "
1. 1 ⊢ A ∧ B, hypo.
2. 1 ⊢ A, conj_eliml 1.
3. 1 ⊢ B, conj_elimr 1.
4. 1 ⊢ B ∧ A, conj_intro 3 2.
5. ⊢ A ∧ B → B ∧ A, subj_intro 4.
"),
("01.37", OK, "
1. 1 ⊢ A ∨ B, hypo.
2. 2 ⊢ A, hypo.
3. 2 ⊢ B ∨ A, disj_intror 2.
4. 4 ⊢ B, hypo.
5. 4 ⊢ B ∨ A, disj_introl 4.
6. 1 ⊢ B ∨ A, disj_elim 1 3 5.
7. ⊢ A ∨ B → B ∨ A, subj_intro 6.
"),
("01.38", OK, "
1. 1 ⊢ ¬B, hypo.
2. 2 ⊢ A → B, hypo.
3. 3 ⊢ A, hypo.
4. 2, 3 ⊢ B, subj_elim 2 3.
5. 2, 1, 3 ⊢ ⊥, neg_elim 1 4.
6. 2, 1 ⊢ ¬A, neg_intro 5.
7. 2 ⊢ ¬B → ¬A, subj_intro 6.
8. ⊢ (A → B) → ¬B → ¬A, subj_intro 7.
"),

("02.01", ELOGIC, "
1. 1 ⊢ A, hypo.
2. ⊢ B → A, subj_intro 1.
"),
("02.02", ELOGIC, "
1. 1 ⊢ A, hypo.
2. ⊢ A → B, subj_intro 1.
"),
("02.03", ELOGIC, "
1. 1 ⊢ A ∧ B, hypo.
2. ⊢ A ∧ A → A ∧ A, subj_intro 1.
")
];
