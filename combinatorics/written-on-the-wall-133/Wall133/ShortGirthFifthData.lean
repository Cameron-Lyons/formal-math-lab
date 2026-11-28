module

public import Wall133.ShortGirthCertificateData

@[expose] public section

namespace Wall133.FifthCertificate

abbrev Fact := Wall133.FourthCertificate.Fact
abbrev Holds {V : Type*} (G : SimpleGraph V) (f : ℕ → V) :=
  Wall133.FourthCertificate.Holds G f

/-- The first six labels form a path. Vertices 6–9 branch at its first
endpoint, and vertices 10–11 at its last. Pairs of further neighbors were
chosen at vertices 6, 7, 8, and 10. -/
def inputs : List Fact := [
  .edge 0 1, .edge 0 6, .edge 0 7, .edge 0 8, .edge 0 9,
  .edge 1 2, .edge 2 3, .edge 3 4, .edge 4 5, .edge 5 10,
  .edge 5 11, .edge 6 12, .edge 6 13, .edge 7 14, .edge 7 15,
  .edge 8 16, .edge 8 17, .edge 10 18, .edge 10 19, .distinct 0 3,
  .distinct 0 4, .distinct 0 5, .distinct 0 10, .distinct 0 11, .distinct 0 12,
  .distinct 0 13, .distinct 0 14, .distinct 0 15, .distinct 0 16, .distinct 0 17,
  .distinct 1 5, .distinct 1 6, .distinct 1 7, .distinct 1 8, .distinct 1 9,
  .distinct 1 10, .distinct 2 4, .distinct 2 5, .distinct 2 6, .distinct 2 7,
  .distinct 2 8, .distinct 2 10, .distinct 3 5, .distinct 3 6, .distinct 3 8,
  .distinct 3 10, .distinct 4 6, .distinct 4 7, .distinct 4 8, .distinct 4 10,
  .distinct 4 11, .distinct 5 6, .distinct 5 7, .distinct 5 8, .distinct 5 18,
  .distinct 5 19, .distinct 6 7, .distinct 6 8, .distinct 6 9, .distinct 7 8,
  .distinct 7 9, .distinct 8 9, .distinct 10 11, .distinct 12 13, .distinct 14 15,
  .distinct 16 17, .distinct 18 19, .nonedge 0 2, .nonedge 0 3, .nonedge 0 4,
  .nonedge 0 5, .nonedge 0 12, .nonedge 0 13, .nonedge 0 14, .nonedge 0 15,
  .nonedge 0 16, .nonedge 0 17, .nonedge 1 3, .nonedge 1 4, .nonedge 1 5,
  .nonedge 1 6, .nonedge 1 7, .nonedge 1 8, .nonedge 1 9, .nonedge 2 4,
  .nonedge 2 5, .nonedge 2 6, .nonedge 2 7, .nonedge 2 8, .nonedge 2 9,
  .nonedge 3 5, .nonedge 3 10, .nonedge 3 11, .nonedge 4 10, .nonedge 4 11,
  .nonedge 5 18, .nonedge 5 19, .nonedge 6 3, .nonedge 6 4, .nonedge 6 5,
  .nonedge 6 7, .nonedge 6 8, .nonedge 6 9, .nonedge 7 5, .nonedge 7 8,
  .nonedge 7 9, .nonedge 8 3, .nonedge 8 5, .nonedge 8 9, .nonedge 9 3,
  .nonedge 10 0, .nonedge 10 11, .nonedge 11 2, .nonedge 12 13, .nonedge 14 15,
  .nonedge 16 17, .nonedge 18 19]

end Wall133.FifthCertificate
