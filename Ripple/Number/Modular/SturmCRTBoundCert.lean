/-
  Certificate-based proof of the final recurrence coefficient array bound.
  Self-contained — does not import SturmCRTBound.lean.
-/
import Ripple.Number.Modular.SturmQrowCertBridge

namespace Ripple
namespace Number
namespace Modular

-- Re-export the final bound theorem from Bridge
-- This is the key result: all entries of phi41Level41RecurrenceCoeffArray are bounded.
-- It implies all entries are 0 when combined with the CRT mod-p certificates.
#check QrowCert_recurrence_array_abs_le_bound
#check Qrow_bound_big_array
#check Qrow_bound_pull_array

end Modular
end Number
end Ripple
