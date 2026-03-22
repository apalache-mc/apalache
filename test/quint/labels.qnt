module labels {
  var x: int

  action init = any {
    pure val __label_x0 = true
    x' = 0,
    pure val __label_x1 = true
    x' = 1,
  }

  action step = any {
    pure val __label_inc = true
    x' = x + 1,
    pure val __label_dec = true
    x' = x - 1,
  }

  // this invariant can be violated, but a violation requires 10 steps
  val inv = and {
    pure val __label_above_min = true
    x >= -10,
    pure val __label_below_max = true
    x <= 10,
  }
}
