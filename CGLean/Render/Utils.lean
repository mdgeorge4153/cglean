import ProofWidgets.Data.Svg
import CGLean.Classes.Floatable
open ProofWidgets Svg

instance: Append (Svg frame) where
  -- TODO: what about index map?
  append s1 s2 := { elements := s1.elements ++ s2.elements }

