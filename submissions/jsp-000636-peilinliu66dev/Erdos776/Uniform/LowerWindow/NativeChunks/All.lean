import Erdos776.Uniform.LowerWindow.NativeChunks.R029
import Erdos776.Uniform.LowerWindow.NativeChunks.R061
import Erdos776.Uniform.LowerWindow.NativeChunks.R093
import Erdos776.Uniform.LowerWindow.NativeChunks.R125
import Erdos776.Uniform.LowerWindow.NativeChunks.R157
import Erdos776.Uniform.LowerWindow.NativeChunks.R189
import Erdos776.Uniform.LowerWindow.NativeChunks.R221
import Erdos776.Uniform.LowerWindow.NativeChunks.R253
import Erdos776.Uniform.LowerWindow.NativeChunks.R285
import Erdos776.Uniform.LowerWindow.NativeChunks.R317
import Erdos776.Uniform.LowerWindow.NativeChunks.R349

namespace Erdos776.Uniform

theorem lowerWindowNativeAll :
    (List.range 349).all (fun d => lowerWindowCheck (29 + d)) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  have hlim : d < 349 := List.mem_range.mp hd
  by_cases h29 : d < 32
  · exact lowerWindowNative029 (29 + d) (by omega) (by omega)
  by_cases h61 : d < 64
  · exact lowerWindowNative061 (29 + d) (by omega) (by omega)
  by_cases h93 : d < 96
  · exact lowerWindowNative093 (29 + d) (by omega) (by omega)
  by_cases h125 : d < 128
  · exact lowerWindowNative125 (29 + d) (by omega) (by omega)
  by_cases h157 : d < 160
  · exact lowerWindowNative157 (29 + d) (by omega) (by omega)
  by_cases h189 : d < 192
  · exact lowerWindowNative189 (29 + d) (by omega) (by omega)
  by_cases h221 : d < 224
  · exact lowerWindowNative221 (29 + d) (by omega) (by omega)
  by_cases h253 : d < 256
  · exact lowerWindowNative253 (29 + d) (by omega) (by omega)
  by_cases h285 : d < 288
  · exact lowerWindowNative285 (29 + d) (by omega) (by omega)
  by_cases h317 : d < 320
  · exact lowerWindowNative317 (29 + d) (by omega) (by omega)
  exact lowerWindowNative349 (29 + d) (by omega) (by omega)
end Erdos776.Uniform
#print axioms Erdos776.Uniform.lowerWindowNativeAll
