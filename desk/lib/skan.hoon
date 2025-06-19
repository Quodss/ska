/-  *noir
::
=*  stub  !!
=*  one  `@`1
::
|%
+$  blocklist  (jug @uxsite @uxsite)       ::  redo blacklist parent -> children
+$  state
  $:  =evals
      juggled=(set @uxsite)                ::  evalsites whose product is used as code
      site=@uxsite                         ::  current evalsite index
      quasi=(list (pair @uxsite @uxsite))  ::  supposedly equal child and parent of recursive loop
  ==
::  +juggle: walk the formula, generating eval sites
::  and recording products of which evalsites are used as code
::
++  juggle
  =|  =blocklist
  |=  [bus=sock fol=*]
  ^-  state
  =*  redo-loop  $
  =;  gen
    =^  redo=(list (pair @uxsite @uxsite))  gen  (final gen)
    ?~  redo  gen
    redo-loop(blocklist (~(gas ju blocklist) redo))
  ::
  =<  +
  =|  gen=state
  =|  stack=(list (trel sock * @uxsite))
  |-  ^-  [sock-source state]
  =*  eval-loop  $
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  =.  sites.evals.gen  (~(put by sites.evals.gen) here-site sock.sub fol)
  =.  calls.evals.gen  (~(add ja calls.evals.gen) fol here-site sock.sub)
  =.  stack  [[sock.sub fol here-site] stack]
  ::
  |^  ^-  [sock-source _gen]
  =*  fol-loop  $
  ?+    fol  [[|+~ ~] gen]
      [p=^ q=*]
    =^  a=sock-source  gen  $(fol p.fol)
    =^  b=sock-source  gen  $(fol q.fol)
    :_  gen
    [(~(knit so sock.a) sock.b) [one here-site]~ source.a source.b]
  ::  %0, %1
  ::  ...
  ::
      [%2 s=* f=*]
    =^  sub1=sock-source  gen  $(fol s.fol)
    =^  fol1=sock-source  gen  $(fol f.fol)
    ?.  =(& cape.sock.fol1)
      ::  indirect call
      ::
      [[|+~ ~] gen]
    ::  direct call
    ::  record what eval sites generated the formula we are about to eval
    ::
    =/  fol-src-sites
      =/  src  source.fol1
      |-  ^-  (list @uxsite)
      ?~  src  ~
      (zing (turn n.src tail) $(src l.src) $(src r.src) ~)
    ::
    =.  juggled.gen  (~(gas in juggled.gen) fol-src-sites)
    ::  check for loop:
    ::    check if there is formula in the stack above us that has a
    ::    quasi-compatible sock (heuristic), if yes we guess that this is a loop
    ::    and record both socks.
    ::    when finalizing, check that the differing parts of socks are not
    ::    used as code
    ::    if they are, the guess was wrong, redo the analysis, putting the sock
    ::    in the blacklist
    ::
    =/  future-site  site.gen
    =/  s  stack
    |-  ^-  [sock-source _gen]
    =*  stack-loop  $
    ?^  s
      ::  quasi-loop condition:
      ::  equal formulas, not in the blacklist, quasi matching subjects
      ::
      ?.  ?&  =(q.i.s data.sock.fol1)
              !(~(has ju block.gen) here-site future-site)
              (close sock.sub p.i.s)
          ==
        stack-loop(s t.s)
      =*  f  data.sock.fol1
      =.  sites.evals.gen  (~(put by sites.evals.gen) future-site sock.sub f)
      =.  calls.evals.gen  (~(add ja calls.evals.gen) f future-site sock.sub)
      =.  quasi.gen  [[future-site here-site] quasi.gen]
      [[|+~ ~] gen]
    ::  non-loop case: analyse through, attach provenance info
    ::
    =^  res  gen
      %=  eval-loop
        sub  sub1
        fol  data.sock.fol1
      ==
    :_  gen
    :-  sock.res
    =/  from-here=[@axis @uxsite]  [one future-site]
    ?~  source.res  [~[from-here] ~ ~]
    =*  src  source.res
    [[from-here n.src] l.src r.src]
  ::
    [%9 b=@ c=*]
  $(fol [7 c.fol 2 [0 1] 0 b.fol])
  ==
  ::  +close: socks are suspiciously similar. Loop heuristic
  ::
  ++  close
    |=  [here=sock there=sock]
    ^-  ?
    stub
  --
::
++  final
  |=  gen=state
  ^-  [(list (pair @uxsite @uxsite)) state]
  stub
--