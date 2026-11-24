import Wall133.ShortGirthStars

namespace Wall133.FourthCertificate

/-- Facts about a labelled configuration of core neighbors at a four-edge geodesic. -/
inductive Fact where
  | edge (i j : ℕ)
  | nonedge (i j : ℕ)
  | distinct (i j : ℕ)
deriving DecidableEq

def Holds {V : Type*} (G : SimpleGraph V) (f : ℕ → V) : Fact → Prop
  | .edge i j => G.Adj (f i) (f j)
  | .nonedge i j => ¬G.Adj (f i) (f j)
  | .distinct i j => f i ≠ f j

/-- The geodesic occupies 0 through 4. Its three branches start at 5, 6, 7.
Vertices 8 through 13 are two children on each branch. The last four labels
are two further neighbors of each of vertices 8 and 9. -/
def inputs : List Fact := [
  .edge 0 1, .edge 0 5, .edge 0 6, .edge 0 7, .edge 1 2,
  .edge 2 3, .edge 3 4, .edge 5 8, .edge 5 9, .edge 6 10,
  .edge 6 11, .edge 7 12, .edge 7 13, .edge 14 8, .edge 15 8,
  .edge 16 9, .edge 17 9, .distinct 5 2, .distinct 5 3, .distinct 5 6,
  .distinct 5 7, .distinct 6 1, .distinct 6 2, .distinct 6 3, .distinct 6 7,
  .distinct 7 1, .distinct 7 2, .distinct 8 0, .distinct 8 1, .distinct 8 2,
  .distinct 8 3, .distinct 8 9, .distinct 9 0, .distinct 9 1, .distinct 9 2,
  .distinct 9 3, .distinct 10 0, .distinct 10 2, .distinct 10 3, .distinct 10 11,
  .distinct 11 0, .distinct 11 2, .distinct 11 3, .distinct 12 0, .distinct 12 2,
  .distinct 12 3, .distinct 12 13, .distinct 13 0, .distinct 13 2, .distinct 14 5,
  .distinct 14 15, .distinct 15 5, .distinct 16 5, .distinct 16 17, .distinct 17 5,
  .nonedge 0 2, .nonedge 0 3, .nonedge 0 4, .nonedge 1 3, .nonedge 1 4,
  .nonedge 2 4, .nonedge 5 1, .nonedge 5 2, .nonedge 5 3, .nonedge 5 4,
  .nonedge 5 6, .nonedge 5 7, .nonedge 6 1, .nonedge 6 2, .nonedge 6 3,
  .nonedge 6 4, .nonedge 6 7, .nonedge 7 1, .nonedge 7 2, .nonedge 7 3,
  .nonedge 7 4, .nonedge 8 0, .nonedge 8 1, .nonedge 8 4, .nonedge 8 9,
  .nonedge 9 0, .nonedge 9 1, .nonedge 9 4, .nonedge 10 0, .nonedge 10 1,
  .nonedge 10 4, .nonedge 11 0, .nonedge 11 1, .nonedge 11 4, .nonedge 12 0,
  .nonedge 12 1, .nonedge 12 4, .nonedge 12 13, .nonedge 13 0, .nonedge 13 1,
  .nonedge 13 4, .nonedge 14 5, .nonedge 14 15, .nonedge 15 5, .nonedge 16 5,
  .nonedge 16 17, .nonedge 17 5]

end Wall133.FourthCertificate
