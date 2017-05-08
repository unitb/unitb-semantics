
import data.stream

import util.data.bijection

import unity.scheduling.basic

namespace scheduling.infinite

open stream scheduling

lemma sched' {lbl : Type} [s : infinite lbl] [nonempty lbl]
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
sorry

end scheduling.infinite
