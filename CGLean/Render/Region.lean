import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay
import CGLean.Classes.Floatable
import CGLean.Classes.Region
import CGLean.Geometry.Point2D

open ProofWidgets Svg

def floatPoint [Floatable α] (p : Point α) : Float × Float := (Floatable.toFloat p.x, Floatable.toFloat p.y)

def toSvg [Floatable α] [Region R (Point α)] (frame : Frame) (r : R) : Svg frame :=
  let nodes : Array (Element frame) := Region.vertices r |> List.map (fun p => circle (floatPoint p) (.abs 0.05) |>.setFill (0.5,0.5,1.)) |> List.toArray
  let edges : Array (Element frame) := Region.segments r |> List.map (fun (p,q) => line (floatPoint p) (floatPoint q) |>.setStroke (0.8, 0.0, 0.0) (.px 2)) |> List.toArray
  { elements := edges ++ nodes }
