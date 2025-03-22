
use crate::{Env, verify, ErrorKind, load_prelude, KEYWORDS};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Expected {Ok, ErrLogic, ErrSyntax}

const OK: Expected = Expected::Ok;
const ELOGIC: Expected = Expected::ErrLogic;
const ESYNTAX: Expected = Expected::ErrSyntax;

#[test]
fn keywords_sorted() {
    fn is_sorted(a: &[(&[u8], &str)]) -> bool {
        let mut i = 1;
        while i < a.len() {
            if a[i-1].0 >= a[i].0 {return false;}
            i += 1;
        }
        true
    }
    assert!(is_sorted(KEYWORDS));
}

#[test]
fn run_test_list() {
    let mut env = Env::new();
    for (test_id, expected, code) in TESTS {
        env.reset();
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
"),

("03.01", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A u, uq_elim 1.
"),
("03.02", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A w, uq_elim 1.
"),
("03.03", OK, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ A x, uq_elim 1.
"),
("03.04", OK, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B u, uq_elim 1.
"),
("03.05", OK, "
1. 1 ⊢ A u, hypo.
2. ⊢ A u → A u, subj_intro 1.
3. ⊢ ∀x. A x → A x, uq_intro 2.
"),
("03.06", OK, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∃x. A x, ex_intro 1.
"),
("03.07", OK, "
1. 1 ⊢ A u ∧ B u, hypo.
2. 1 ⊢ ∃x. A x ∧ B x, ex_intro 1.
"),
("03.08", OK, "
1. 1 ⊢ A u ∧ B u, hypo.
2. 1 ⊢ A u, conj_eliml 1.
3. 1 ⊢ B u, conj_elimr 1.
4. 1 ⊢ B u ∧ A u, conj_intro 3 2.
5. 1 ⊢ ∃x. B x ∧ A x, ex_intro 4.
6. 6 ⊢ ∃x. A x ∧ B x, hypo.
7. 6 ⊢ ∃x. B x ∧ A x, ex_elim 6 5.
8. ⊢ (∃x. A x ∧ B x) → (∃x. B x ∧ A x), subj_intro 7.
"),
("03.09", OK, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B u, uq_elim 1.
3. 1 ⊢ A u, conj_eliml 2.
4. 1 ⊢ B u, conj_elimr 2.
5. 1 ⊢ B u ∧ A u, conj_intro 4 3.
6. 1 ⊢ ∀x. B x ∧ A x, uq_intro 5.
7. ⊢ (∀x. A x ∧ B x) → (∀x. B x ∧ A x), subj_intro 6.
"),
("03.10", OK, "
1. 1 ⊢ ∀x. A ∧ P x, hypo.
2. 1 ⊢ A ∧ P u, uq_elim 1.
3. 1 ⊢ A, conj_eliml 2.
4. 1 ⊢ P u, conj_elimr 2.
5. 1 ⊢ ∀x. P x, uq_intro 4.
6. 1 ⊢ A ∧ ∀x. P x, conj_intro 3 5.
const_conj. ⊢ (∀x. A ∧ P x) → A ∧ (∀x. P x), subj_intro 6.
"),
("03.11", OK, "
1. 1 ⊢ ∃x. P x ∧ Q x, hypo.
2. 2 ⊢ P u ∧ Q u, hypo.
3. 2 ⊢ P u, conj_eliml 2.
4. 2 ⊢ Q u, conj_elimr 2.
5. 2 ⊢ ∃x. P x, ex_intro 3.
6. 2 ⊢ ∃x. Q x, ex_intro 4.
7. 2 ⊢ (∃x. P x) ∧ (∃x. Q x), conj_intro 5 6.
8. 1 ⊢ (∃x. P x) ∧ (∃x. Q x), ex_elim 1 7.
9. ⊢ (∃x. P x ∧ Q x) → (∃x. P x) ∧ (∃x. Q x), subj_intro 8.
"),
("03.12", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ B x → B x, 1.
"),
("03.13", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A y → A y, 1.
"),
("03.14", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ B y → B y, 1.
"),
("03.15", OK, "
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → x ∈ A, 1.
"),
("03.16", OK, "
1. ⊢ P x A → P x A, axiom.
2. ⊢ y ∈ A → y ∈ A, 1.
"),
("03.17", OK, "
1. ⊢ P x A → P x A, axiom.
2. ⊢ y ∈ B → y ∈ B, 1.
"),
("03.18", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀x. A x, 1.
"),
("03.19", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀y. A y, 1.
"),
("03.20", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀x. B x, 1.
"),
("03.21", OK, "
1. ⊢ ∀x. A x, axiom.
2. ⊢ ∀y. B y, 1.
"),

("04.01", ELOGIC, "
1. 1 ⊢ ∀x. A x, hypo.
2. 1 ⊢ B u, uq_elim 1.
"),
("04.02", ELOGIC, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ A u, uq_elim 1.
"),
("04.03", ELOGIC, "
1. 1 ⊢ ∀x. A x ∧ B x, hypo.
2. 1 ⊢ A u ∧ B w, uq_elim 1.
"),
("04.04", ELOGIC, "
1. 1 ⊢ A u, hypo.
2. 1 ⊢ ∀x. A x, uq_intro 1.
"),
("04.05", ELOGIC, "
1. 1 ⊢ B u, hypo.
2. 1 ⊢ ∃x. A x, ex_intro 1.
"),
("04.06", ELOGIC, "
1. 1 ⊢ A x, hypo.
2. ⊢ A x → A y, subj_intro 1.
"),
("04.07", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → B x, 1.
"),
("04.08", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → A y, 1.
"),
("04.09", ELOGIC, "
1. ⊢ A x → A x, axiom.
2. ⊢ A x → B y, 1.
"),
("04.10", ELOGIC, "
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → x ∈ B, 1.
"),
("04.11", ELOGIC, "
1. ⊢ P x A → P x A, axiom.
2. ⊢ x ∈ A → y ∈ A, 1.
"),
("04.12", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ B x, 1.
"),
("04.13", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ A y, 1.
"),
("04.14", ELOGIC, "
1. 1 ⊢ A x, axiom.
2. 1 ⊢ B y, 1.
"),

("05.01", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a) → A (f a), 1.
"),
("05.02", OK, "
0. ⊢ f x = some_function, def.
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a) → A (f a), 1.
"),
("05.03", OK, "
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a b) → A (f a b), 1.
"),
("05.04", OK, "
0. ⊢ f x y = some_function, def.
1. ⊢ A x → A x, axiom.
2. ⊢ A (f a b) → A (f a b), 1.
"),
("05.05", OK, "
0. |- add x y = some_function, def.
1. |- x = x, axiom.
2. |- a + b = a + b, 1.
"),
("05.06", OK, "
0. |- add x y = some_function, def.
1. |- A x → A x, axiom.
2. |- A (a + b) → A (a + b), 1.
"),

("06.01", ELOGIC, "
0. ⊢ p x ↔ some_predicate, def.
1. ⊢ p x → p x, axiom.
2. ⊢ A x → A x, 1.
"),
("06.02", ELOGIC, "
0. ⊢ add x y = some_function, def.
1. ⊢ x = x, axiom.
2. ⊢ a + b = a + c, 1.
"),
("06.03", ELOGIC, "
0. ⊢ add x y = some_function, def.
1. ⊢ x = x, axiom.
2. ⊢ x = a, 1.
"),
("06.04", ELOGIC, "
0. ⊢ add x y = some_function, def.
1. ⊢ A x → A x, axiom.
2. ⊢ A (a + b) → A (a + c), 1.
"),
("06.05", ELOGIC, "
1. ⊢ f x → f (¬A), axiom.
"),
("06.06", ELOGIC, "
1. ⊢ f x y → f (¬A) y, axiom.
"),
("06.07", ELOGIC, "
1. ⊢ f x y → f x (¬A), axiom.
"),
/* ("06.08", ELOGIC, "
1. ⊢ f x, axiom.
2. ⊢ f (¬A), 1.
"),
("06.09", ELOGIC, "
1. ⊢ f x y, axiom.
2. ⊢ f (¬A) y, 1.
"),
("06.10", ELOGIC, "
1. ⊢ f x y, axiom.
2. ⊢ f x (¬A), 1.
"), */

("07.01", OK, "
0. ⊢ a = some_constant, def.
0. ⊢ b = some_constant, def.
0. ⊢ x + y = some_function, def.
c_eq. ⊢ c = a + b, def.
"),
("07.02", OK, "
0. ⊢ a = some_constant, def.
0. ⊢ b = some_constant, def.
0. ⊢ x + y = some_function, def.
p_equi. ⊢ p ↔ a = b, def.
"),
("07.03", OK, "
0. ⊢ p x ↔ some_predicate, def.
0. ⊢ q x ↔ some_predicate, def.
r_equi. ⊢ r x ↔ p x ∧ q x, def.
"),
("07.04", OK, "
0. ⊢ p x ↔ some_predicate, def.
0. ⊢ q x ↔ some_predicate, def.
r_equi. ⊢ r ↔ ∀x. p x ∧ q x, def.
"),
("07.05", OK, "
0. ⊢ f x = some_function, def.
0. ⊢ g x = some_function, def.
h_eq. ⊢ h x = g (f x), def.
"),
("07.06", OK, "
0. ⊢ f x = some_function, def.
0. ⊢ g x = some_function, def.
r_equi. ⊢ r ↔ ∀x. f x = g x, def.
"),

("08.01", ELOGIC, "
1. ⊢ a = b, def.
"),
("08.02", ELOGIC, "
1. ⊢ a = a, def.
"),
("08.03", ELOGIC, "
1. ⊢ p ↔ q, def.
"),
("08.04", ELOGIC, "
1. ⊢ p ↔ p, def.
"),
("08.05", ELOGIC, "
1. ⊢ f x = f x, def.
"),
("08.06", ELOGIC, "
1. ⊢ f x = g x, def.
"),
("08.07", ELOGIC, "
1. ⊢ p x ↔ p x, def.
"),
("08.08", ELOGIC, "
1. ⊢ p x ↔ q x, def.
"),

/*("09.01", ELOGIC, "
1. 1 ⊢ P x, hypo.
2. ⊢ P x → P x, subj_intro 1.
3. ⊢ ∀P. P x → P x, uq_intro 2.
"),*/
("09.02", ELOGIC, "
1. |- A x ∧ x, axiom
")
];
