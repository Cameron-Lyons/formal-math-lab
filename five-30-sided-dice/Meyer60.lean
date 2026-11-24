import FiveDice

namespace FiveDice

/-- Paul Meyer's five 60-sided dice. Each entry is the owner of the next
label. Transcribed from the face table at
https://en.wikipedia.org/wiki/Go_First_Dice#Five_players. -/
def meyer60 : List Die :=
  [
    0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 3, 2, 1, 4, 4, 1, 2, 3, 0, 0,
    0, 0, 4, 2, 1, 3, 3, 1, 2, 4, 4, 2, 1, 3, 3, 1, 2, 4, 0, 0,
    0, 0, 3, 2, 1, 4, 4, 1, 2, 3, 0, 1, 2, 3, 4, 4, 3, 2, 1, 0,
    0, 0, 3, 2, 1, 4, 4, 1, 2, 3, 0, 1, 2, 3, 4, 4, 3, 2, 1, 0,
    0, 4, 2, 3, 1, 1, 3, 2, 4, 0, 4, 2, 3, 1, 1, 3, 2, 4, 0, 0,
    1, 2, 3, 4, 4, 3, 2, 1, 0, 3, 2, 1, 4, 4, 1, 2, 3, 0, 0, 0,
    0, 0, 0, 4, 2, 1, 3, 3, 1, 2, 4, 0, 0, 1, 2, 4, 3, 3, 4, 2,
    1, 3, 2, 4, 1, 1, 4, 2, 3, 0, 0, 3, 2, 4, 1, 1, 4, 2, 3, 1,
    2, 4, 3, 3, 4, 2, 1, 0, 0, 4, 2, 1, 3, 3, 1, 2, 4, 0, 0, 0,
    0, 0, 0, 3, 2, 4, 1, 1, 4, 2, 3, 0, 4, 2, 3, 1, 1, 3, 2, 4,
    0, 0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 1, 2, 3, 4, 4, 3, 2, 1, 0,
    0, 4, 2, 3, 1, 1, 3, 2, 4, 0, 3, 2, 4, 1, 1, 4, 2, 3, 0, 0,
    0, 4, 2, 1, 3, 3, 1, 2, 4, 0, 1, 2, 4, 3, 3, 4, 2, 1, 0, 0,
    0, 0, 3, 2, 4, 1, 1, 4, 2, 3, 3, 2, 4, 1, 1, 4, 2, 3, 0, 0,
    0, 0, 1, 2, 4, 3, 3, 4, 2, 1, 0, 4, 2, 1, 3, 3, 1, 2, 4, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem meyer60_fair : Fair 60 meyer60 := by
  apply (check_iff_fair _ _).mp
  decide +kernel

end FiveDice
