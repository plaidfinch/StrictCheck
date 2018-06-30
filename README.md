  # StrictCheck: Keep Your Laziness In Check
  
  StrictCheck is a property-based random testing framework for
  observing, specifying, and testing the strictness behaviors of Haskell
  functions. Strictness behavior is traditionally considered a non-functional
  property; StrictCheck allows it to be tested as if it were one, by reifying
  demands on data structures so they can be manipulated and examined within
  Haskell.
  
  StrictCheck can specify and test the strictness behavior of any Haskell
  function—including higher-order ones—with only a constant factor of overhead,
  and requires no boilerplate for testing functions on Haskell-standard algebraic
  data types.

  In the paper, we also demonstrate a non-trivial application of our library,
  developing a correct specification of a data structure whose properties
  intrinsically rely on subtle use of laziness: Okasaki's constant-time purely
  functional queue.
