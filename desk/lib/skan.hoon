/-  *noir
::
=*  stub  !!
=*  one  `@`1
::
|%
+$  blocklist  (jug @uxsite @uxsite)       ::  redo blocklist parent -> children
+$  state                                  ::  global state
  $:  =evals
      juggled=(set @uxsite)                ::  evalsites whose product is used as code
      site=@uxsite                         ::  current evalsite index
      quasi=(list (pair @uxsite @uxsite))  ::  supposedly equal child and parent of recursive loop
  ==
::  +juggle: walk the formula, generating eval sites
::  and recording which evalsites produced code
::  i.e. their products were used as code
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
  =|  stack=(list (trel sock * @uxsite))  ::  lexically scoped
  =/  sub=sock-anno  [bus ~ ~]
  |-  ^-  [sock-anno state]
  =*  eval-loop  $
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  ::  record current evalsite in the subject provenance tree
  ::
  =.  src.sub
    ?~  src.sub  [[one here-site]~ ~ ~]
    src.sub(n [[one here-site] n.src.sub])
  ::  register evalsite in bidirectional mapping
  ::
  =.  sites.evals.gen  (~(put by sites.evals.gen) here-site sock.sub fol)
  =.  calls.evals.gen  (~(add ja calls.evals.gen) fol here-site sock.sub)
  ::
  ::  TODO check memo/melo caches
  ::
  =.  stack  [[sock.sub fol here-site] stack]
  ::
  |^  ^-  [sock-anno _gen]
  =*  fol-loop  $
  ?+    fol  [[|+~ ~ ~] gen]
      [p=^ q=*]
    =^  a=sock-anno  gen  fol-loop(fol p.fol)
    =^  b=sock-anno  gen  fol-loop(fol q.fol)
    :_  gen
    :+  (~(knit so sock.a) sock.b)
      [[one here-site]~ sik.a sik.b]
    ::  tree normalization idiom
    ::
    =-  ?:(=([~ ~ ~] -) ~ -)
    [~ src.a src.b]
  ::  %0, %1
  ::  ...
  ::
      [%2 s=* f=*]
    =^  sub-new=sock-anno  gen  fol-loop(fol s.fol)
    =^  lof-new=sock-anno  gen  fol-loop(fol f.fol)
    ?.  =(& cape.sock.lof-new)
      ::  indirect call
      ::
      [[|+~ ~ ~] gen]
    ::  direct call
    ::
    =/  fol-new=*  data.sock.lof-new
    ::  record what eval sites generated the formula we are about to eval
    ::
    =/  fol-src-sites
      =/  s  sik.lof-new
      |-  ^-  (list @uxsite)
      ?~  s  ~
      (zing (turn n.s tail) $(s l.s) $(s r.s) ~)
    ::
    =.  juggled.gen  (~(gas in juggled.gen) fol-src-sites)
    ::  check for loop:
    ::    check if there is formula in the stack above us that has a
    ::    quasi-compatible sock (heuristic), if yes we guess that this is a loop
    ::    and record both socks.
    ::    when finalizing, check that the differing parts of socks are not
    ::    used as code
    ::    if they are, the guess was wrong, redo the analysis, putting the sock
    ::    in the blocklist
    ::
    ::  allocate an evalsite in advance, as we might not enter eval-loop
    ::
    =/  future-site  site.gen
    =/  tak  stack
    |-  ^-  [sock-anno _gen]
    =*  stack-loop  $
    ?^  tak
      ::  quasi-loop condition:
      ::  equal formulas, not in the blocklist, quasi matching subjects
      ::
      ?.  ?&  =(q.i.tak fol-new)
              !(~(has ju blocklist) r.i.tak future-site)
              (close sock.sub-new p.i.tak)
          ==
        stack-loop(tak t.tak)
      =*  f  fol-new
      =*  s  sock.sub-new
      ::  we "enter" eval-loop here by registering the evalsite and immediately
      ::  producing the result sock, and also register quasi match for future
      ::  verification
      ::
      =.  sites.evals.gen  (~(put by sites.evals.gen) future-site s f)
      =.  calls.evals.gen  (~(add ja calls.evals.gen) f future-site s)
      =.  quasi.gen  [[future-site r.i.tak] quasi.gen]
      [[|+~ ~ ~] gen]
    ::  non-loop case: analyse through, attach product provenance info
    ::
    =^  res=sock-anno  gen
      %=  eval-loop
        sub  sub-new
        fol  fol-new
      ==
    ::
    =.  sik.res
      =/  from-there=[@axis @uxsite]  [one future-site]
      ?~  sik.res  [~[from-there] ~ ~]
      [[from-there n.sik.res] l.sik.res r.sik.res]
    ::
    [res gen]
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