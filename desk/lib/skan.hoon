/-  *noir
::
::  TODO:
::    move redo-loop into arm-loop
::    nock formula cases fill
::    final, memo, process (prob noop/identity)
::    
=*  stub  !!
=*  one  `@`1
=/  dunno  [|+~ ~ ~]  ::  ignorant sock-anno
::
|%
::  redo blocklist parent -> children
::
+$  blocklist  (jug @uxsite @uxsite)
++  error
  |$  [m]
  (each m (pair @uxsite @uxsite))
::
+$  err-state  (error state)
+$  state
  ::  global state
  ::    evals:    call info
  ::    results:  result table
  ::    site:     eval index generator
  ::    cycles:
  ::      key: top-most entry into a cyclical call graph
  ::      val:
  ::        guess: parent -> kids mapping of loop assumptions
  ::        points: all vertices of the cyclical call graph
  ::      when new assumptions are made, we either extend an old cycle
  ::      or add a new one if its finalization does not depend on previous cycles
  ::      thus when we finish analysis of a site which is present as a key
  ::      in cycles, we can finalize that loop independently of other loops
  ::
  ::    need: evalsite subject requirements
  ::
  $:  =evals
      =results
      site=@uxsite
      cycles=(map @uxsite cycle)
      need=(map @uxsite cape)
  ==
::
+$  cycle  [guess=(jug @uxsite @uxsite) points=(set @uxsite)]
::
+$  stack
  ::  list: linear stack of evalsites. XX more representations for performance?
  ::    
  $:  list=(list @uxsite)
  ==
::
++  scan
  =|  =blocklist
  |=  [bus=* fol=*]
  ^-  state
  =*  redo-loop  $
  =;  lys=err-state
    ?-  -.lys
      %&  p.lys
      %|  redo-loop(blocklist (~(put ju blocklist) p.lys))
    ==
  ::
  =|  gen=state
  =|  =stack  ::  lexically scoped
  =/  sub=sock-anno  [&+bus ~ ~]
  ::  an eval'd formula is loopy if it was estimated to call something that is
  ::  already on the stack or it called a loopy formula.
  ::  a loopy formula cannot be finalized unless it is the loop's starting point
  ::
  =;  res-eval
    ?:  ?=(%| -.res-eval)  res-eval
    ::  debug asserts
    ::
    ?>  =(0x0 site.p.res-eval)
    ?>  =(~ cycles.gen.p.res-eval)
    &+gen.p.res-eval
  |-  ^-  (error [[site=@uxsite res=sock-anno loopy=?] gen=state])
  =*  eval-loop  $
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  =;  tagless-res
    ?:  ?=(%| -.tagless-res)  tagless-res
    &+[[here-site -.p.tagless-res] +.p.tagless-res]
  ^-  (error [[sock-anno ?] state])
  ::  record current evalsite in the subject provenance tree
  ::
  =.  src.sub
    ?~  src.sub  [[one here-site]~ ~ ~]
    src.sub(n [[one here-site] n.src.sub])
  ::  start tracking subject capture
  ::
  =.  tok.sub  1
  ::  register evalsite in bidirectional mapping
  ::
  =.  sites.evals.gen  (~(put by sites.evals.gen) here-site sock.sub fol ~)
  =.  calls.evals.gen  (~(add ja calls.evals.gen) fol here-site sock.sub ~)
  ::  check memo cache
  ::
  ?^  m=(memo here-site fol sub gen)  &+[[pro.u.m |] gen.u.m]
  =.  list.stack  [here-site list.stack]
  =/  res-fol=(error [[code=nomm prod=sock-anno loopy=?] gen1=state])
    |-  ^-  (error [[nomm sock-anno ?] state])
    =*  fol-loop  $
    ?+    fol  &+[[[%0 0] dunno |] gen]
        [p=^ q=^]
      stub
    ::
        [%2 p=^ q=^]
      stub
    ::
        [%9 p=@ q=^]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ==
  ::
  ?:  ?=(%| -.res-fol)  res-fol
  =.  gen  gen1.p.res-fol
  ::  save results
  ::
  =,  p.res-fol
  =.  results.gen  (~(put by results.gen) here-site code prod)
  =;  =err-state
    ?:  ?=(%| -.err-state)  err-state
    &+[[prod loopy] p.err-state]
  ?.  loopy  (final here-site prod ~ gen)
  ?~  cycle=(~(get by cycles.gen) here-site)  (process here-site prod gen)
  (final here-site prod cycle gen)
::  finalize analysis of either non-loopy formula or a loop entry
::
++  final
  |=  [site=@uxsite prod=sock-anno cyc=(unit cycle) gen=state]
  ^-  err-state
  stub
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  [site=@uxsite prod=sock-anno gen=state]
  ^-  err-state
  stub
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state]
  ^-  (unit [pro=sock-anno gen=state])
  stub
--