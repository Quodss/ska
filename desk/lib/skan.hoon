/-  *noir
::
::  TODO:
::    final, memo, process, close (prob noop/identity)
::    %2 push need in direct branch
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
  ::    cycles:   stack of call graph cycles
  ::      entry: top-most entry into a cyclical call graph
  ::      cycle: set of parent-kid pairs of loop assumptions
  ::
  ::      when new assumptions are made, we either extend an old cycle
  ::      or add a new one if its finalization does not depend on previous cycles
  ::      thus when we finish analysis of a site which is recorded as an entry
  ::      in `cycles`, we can finalize that loop independently of loops
  ::      deeper in the stack
  ::
  ::    need: evalsite subject requirements
  ::
  $:  =evals
      =results
      site=@uxsite
      cycles=(list [entry=@uxsite =cycle])
      need=(map @uxsite cape)
  ==
::
+$  cycle  (list [par=@uxsite kid=@uxsite])
::
+$  stack
  ::  list: linear stack of evalsites. XX more representations for performance?
  ::    
  $:  list=(list (trel sock * @uxsite))
  ==
::
++  scan
  |=  [bus=* fol=*]
  ^-  state
  =|  gen=state
  =|  =stack  ::  lexically scoped
  =/  sub=sock-anno  [&+bus ~ ~]
  =;  res-eval
    ::  debug asserts
    ::
    ?>  =(~ cycles.gen.res-eval)
    gen.res-eval
  ::  a formula is loopy if it is a Nock 2 that was estimated to be a loop or
  ::  if the formula contains a loopy formula.
  ::  if eval'd formula is loopy then it cannot be finalized unless it is
  ::  an entry point into a loop, in which case it is finalized by checking
  ::  the assumptions made when analyzing the call graph cycle. entry points
  ::  and assumptions are recorded in cycles.gen
  ::
  ::  invariant: if a formula is loopy then cycles.gen is not empty and its
  ::  first element is the cycle we are currently in
  ::
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  ?>  =(0x0 here-site)
  |-  ^-  [[res=sock-anno loopy=?] gen=state]
  =*  eval-loop  $
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  =|  =blocklist
  |-  ^-  [[res=sock-anno loopy=?] gen=state]
  =*  redo-loop  $
  =;  res
    ?-  -.res
      %&  p.res
      %|  redo-loop(blocklist (~(put ju blocklist) p.res))
    ==
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
  =.  list.stack  [[sock.sub fol here-site] list.stack]
  =^  [code=nomm prod=sock-anno loopy=?]  gen
    |-  ^-  [[nomm sock-anno ?] state]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] dunno |] gen]
        [p=^ q=^]
      =^  [l-code=nomm l-prod=sock-anno l-loopy=?]  gen  fol-loop(fol p.fol)
      =^  [r-code=nomm r-prod=sock-anno r-loopy=?]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [l-code r-code]
        :+  (~(knit so sock.l-prod) sock.r-prod)
          (cons:source src.l-prod src.r-prod)
        (cons:took tok.l-prod tok.r-prod)
      |(l-loopy r-loopy)
    ::
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol dunno |] gen]
      :_  gen
      :+  fol
        :+  (~(pull so sock.sub) p.fol)
          (slot:source src.sub p.fol)
        (slot:took tok.sub p.fol)
      |
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol ~ ~] |]
    ::
        [%2 p=^ q=^]
      =^  [s-code=nomm s-prod=sock-anno s-loopy=?]  gen  fol-loop(fol p.fol)
      =^  [f-code=nomm f-prod=sock-anno f-loopy=?]  gen  fol-loop(fol q.fol)
      =^  there-site  gen  [site.gen gen(site +(site.gen))]
      ?.  =(& cape.sock.f-prod)
        ::  indirect call
        ::
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        |(s-loopy f-loopy)
      ::  direct call
      ::
      =/  fol-new  data.sock.f-prod
      ::  XX push need
      ::
      ::  check for loop:
      ::    Check if there is formula in the stack above us that has a
      ::    quasi-compatible sock (heuristic), if yes we guess that this is
      ::    a loop and record both socks.
      ::
      ::    When finalizing, check that the differing parts of socks are not
      ::    used as code.
      ::
      ::    If they are, the guess was wrong, redo the analysis, putting
      ::    the parent-child pair in the blocklist
      ::
      =/  tak  list.stack
      |-  ^-  [[nomm sock-anno ?] state]
      =*  stack-loop  $
      ?^  tak
        ::  loop heuristic:
        ::  equal formulas, not in the blocklist, quasi matching subjects
        ::
        ?.  ?&  =(q.i.tak fol-new)
                !(~(has ju blocklist) r.i.tak there-site)
                (close sock.s-prod p.i.tak gen)
            ==
          stack-loop(tak t.tak)
        ::  draft: loop calls are rendered indirect
        ::  TODO direct loops like in orig
        ::
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        |(s-loopy f-loopy)
      ::  non-loop case: analyse through
      ::
      =^  [pro=sock-anno loopy=?]  gen
        %=  eval-loop
          sub        s-prod
          fol        fol-new
          here-site  there-site
        ==
      :_  gen
      :+  [%2 s-code f-code there-site]
        pro
      |(loopy s-loopy f-loopy)
    ::
        [%3 p=^]
      =^  [p-code=nomm * p-loopy=?]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%3 p-code]
        dunno
      p-loopy
    ::
        [%4 p=^]
      =^  [p-code=nomm * p-loopy=?]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%4 p-code]
        dunno
      p-loopy
    ::
        [%5 p=^ q=^]
      =^  [p-code=nomm * p-loopy=?]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-loopy=?]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%5 p-code q-code]
        dunno
      |(p-loopy q-loopy)
    ::
        [%6 c=^ y=^ n=^]
      =^  [c-code=nomm * c-loopy=?]       gen  fol-loop(fol c.fol)
      =^  [y-code=nomm y-prod=sock-anno y-loopy=?]  gen  fol-loop(fol y.fol)
      =^  [n-code=nomm n-prod=sock-anno n-loopy=?]  gen  fol-loop(fol n.fol)
      :_  gen
      ::  any of yes/no branches' code could be used, this is why we 
      ::  unionize the provenance trees
      ::
      =/  uni-source  (uni:source src.y-prod src.n-prod)
      ::  product sock is an intersection
      ::
      =/  int-sock  (~(purr so sock.y-prod) sock.n-prod)
      :+  [%6 c-code y-code n-code]
        :+  int-sock
          ::  mask unified provenance tree with intersection cape
          ::
          (mask:source uni-source cape.int-sock)
        ::  `took` records subject capture, so we intersect
        ::
        (int:took tok.y-prod tok.n-prod)
      |(c-loopy y-loopy n-loopy)
    ::
        [%7 p=^ q=^]
      =^  [p-code=nomm p-prod=sock-anno p-loopy=?]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm q-prod=sock-anno q-loopy=?]  gen
        fol-loop(fol q.fol, sub p-prod)
      ::
      :_  gen
      :+  [%7 p-code q-code]
        q-prod
      |(p-loopy q-loopy)
    ::
        [%8 p=^ q=^]
      fol-loop(fol [%7 [p.fol %0 1] q.fol])
    ::
        [%9 p=@ q=^]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ::
        [%10 [a=@ don=^] rec=^]
      ?:  =(0 a.fol)  [[[%0 0] dunno |] gen]
      =^  [don-code=nomm don-prod=sock-anno don-loopy=?]  gen
        fol-loop(fol don.fol)
      ::
      =^  [rec-code=nomm rec-prod=sock-anno rec-loopy=?]  gen
        fol-loop(fol rec.fol)
      ::
      :_  gen
      :+  [%10 [a.fol don-code] rec-code]
        :+  (~(darn so sock.rec-prod) a.fol sock.don-prod)
          (edit:source src.rec-prod a.fol src.don-prod)
        (edit:took tok.rec-prod a.fol tok.don-prod)
      |(rec-loopy don-loopy)
    ::
        [%11 p=@ q=^]
      =^  [q-code=nomm q-prod=sock-anno q-loopy=?]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%s11 p.fol q-code]
        q-prod
      q-loopy
    ::
        [%11 [a=@ h=^] f=^]
      ::
      =^  [f-code=nomm f-prod=sock-anno f-loopy=?]  gen  fol-loop(fol f.fol)
      =^  [h-code=nomm h-prod=sock-anno h-loopy=?]  gen  fol-loop(fol h.fol)
      :_  gen
      :+  [%d11 [a.fol h-code] f-code]
        f-prod
      |(f-loopy h-loopy)
    ::
        [%12 p=^ q=^]
      =^  [p-code=nomm * p-loopy=?]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-loopy=?]  gen  fol-loop(fol q.fol)
      [[[%12 p-code q-code] dunno |(p-loopy q-loopy)] gen]
    ==
  ::
  ::  save results
  ::
  =.  results.gen  (~(put by results.gen) here-site code prod)
  =;  =err-state
    ?:  ?=(%| -.err-state)  err-state
    &+[[prod loopy] p.err-state]
  ?.  loopy  &+(final-simple here-site prod gen)
  =*  i  i.-.cycles.gen
  ?.  =(here-site entry.i)  &+(process here-site prod gen)
  (final-cycle here-site prod cycle.i gen)
::  finalize analysis of non-loopy formula
::
++  final-simple
  |=  [site=@uxsite prod=sock-anno gen=state]
  ^-  state
  stub
::  finalize analysis of a call graph cycle entry
::
++  final-cycle
  |=  [site=@uxsite prod=sock-anno cyc=cycle gen=state]
  ^-  err-state
  stub
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  [site=@uxsite prod=sock-anno gen=state]
  ^-  state
  stub
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state]
  ^-  (unit [pro=sock-anno gen=state])
  stub
::
++  close
  |=  [kid=sock par=sock gen=state]
  ^-  ?
  stub
--