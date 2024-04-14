(* this module represents regions in the plane that are bounded by line segments
 * regions generalize polgons: they may have multiple disconnected components,
 * they may have holes, and they may have 0- or 1-dimensional features (isolated
 * points or lines)
 *)
module Make (F : Numbers.OrderedField) : sig
  type point = F.number * F.number
  type region

  (* return the region bounded by a convex, non-degenerate polygon, represented
   * as a list of points.  The points should be ordered counter-clockwise around
   * the boundary of the polygon
   *)
  val create       : point list -> region

  (* return the union of two regions. *)
  val union        : region -> region -> region

  (* contains p r returns true if the point p is in the region r *)
  val contains     : point -> region -> bool

  (* find_closest r p returns the closest point to p that does not lie in r. *)
  val find_closest : region -> point -> point

  (* return all of the points on the boundary of a region *)
  val vertices : region -> point list

  (* return all line segments on the boundary of a region *)
  val edges    : region -> (point * point) list
end

