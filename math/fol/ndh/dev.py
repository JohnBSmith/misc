
def uerr_info(A, B, result, subst):
    print("Konnte nicht unifizieren:")
    print(f"    {result.A}\nmit {result.pattern}")
    print("\nKontext:")
    print(f"    {A}")
    print(f"mit {B}")
    print("\nSubstitutionen:")
    print(subst)
    print()
