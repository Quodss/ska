/-  *noir
::
::  TODO:
::    full loop engine (direct call in %2, final-cycle, process)
::    
=*  stub  !!
=*  one  `@`1
::  ignorant sock-anno
::
=/  dunno  [|+~ ~ ~]
::  default flags: not loopy, fully direct
::
=/  deff  [| &]
::
|%
::  redo blocklist parent -> children
::
+$  blocklist  (jug @uxsite @uxsite)
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
::  direct: fully direct, to avoid memoizing evals that are too generic,
::  otherwise more specific evals would not be reanalyzed
::
+$  flags  [loopy=? direct=?]
::  urge: evalsite subject requirements
::
+$  urge  (map @uxsite cape)
::  error: either m or parent-kid pair which turned out to be false
::
++  error
  |$  [m]
  (each m (pair @uxsite @uxsite))
::
+$  err-state  (error state)
::  lazily concatenated list
::
++  deep
  |$  [m]
  $%  [%deep p=(deep m) q=(deep m)]
      [%list p=(list m)]
  ==
::
+$  frond  (deep [par=@uxsite kid=@uxsite])
+$  cycle  [entry=@uxsite latch=@uxsite =frond]
::
++  fold-deep
  |*  [a=(deep) g=_=>(~ |=([* *] +<+))]
  |-  ^+  ,.+<+.g
  ?-  -.a
    %list  (roll p.a g)
    %deep  $(a q.a, g g(+<+ $(a p.a)))
  ==
::
++  add-frond
  |=  [par=@uxsite kid=@uxsite cycles=(list cycle)]
  ^-  (list cycle)
  ?~  cycles  [par kid %list [par kid] ~]~
  ?:  (gth par latch.i.cycles)
    ::  push new cycle
    ::
    [[par kid %list [par kid] ~] cycles]
  ::  extend top cycle
  ::
  =/  new-cycle=cycle
    [(min par entry.i.cycles) kid %deep [%list [par kid] ~] frond.i.cycles]
  =/  rest  t.cycles
  ::
  |-  ^-  (list cycle)
  ?~  rest  [new-cycle ~]
  ?:  (gth entry.new-cycle latch.i.rest)  [new-cycle rest]
  ::  merge overlapping cycles
  ::
  =.  entry.new-cycle  (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle  [%deep frond.new-cycle frond.i.rest]
  $(rest t.rest)
::
+$  state
  ::  global state
  ::    evals:    call info
  ::    results:  result table
  ::    site:     eval index generator
  ::    cycles:   stack of call graph cycles (aka natural loops aka strongly
  ::    connected components)
  ::      entry: top-most entry into a cyclical call graph
  ::      latch: bottom-most evalsite of the cycle
  ::      frond: set of parent-kid pairs of loop assumptions (back edges)
  ::
  ::      When new assumptions are made, we either extend an old cycle, possibly
  ::      merging multiple predecessor cycles, or add a new one if its
  ::      finalization does not depend on previous cycles. Thus, when we finish
  ::      analysis of a site which is recorded as an entry in `cycles`, we only
  ::      have to check top cycle entry and we can finalize that loop
  ::      independently of loops deeper in the stack.
  ::
  ::      New cycle condition for a parent-kid pair:
  ::        parent > latch.i.-.cycles (compare site labels)
  ::      If false, extend top cycle (set latch to kid, entry to
  ::      min(entry, parent)), then iterate over the rest of the list, 
  ::      merging if new cycle overlaps with the predecessor (entry >= latch)
  ::
  ::    want: evalsite subject requirements
  ::
  $:  =evals
      =results
      site=@uxsite
      cycles=(list cycle)
      want=urge
  ==
::
+$  stack
  $:
    ::  list: linear stack of evalsites
    ::    
    list=(list (trel sock * @uxsite))
    ::  fols: search by formula
    ::
    fols=(jar * (pair sock @uxsite))
  ==
::
++  scan
  |=  [bus=* fol=*]  :: no autocons disassembly
  ^-  state
  =|  gen=state
  =|  =stack  ::  lexically scoped
  =/  sub=sock-anno  [&+bus ~ ~]
  =;  res-eval
    ::  debug asserts
    ::
    ?>  =(~ cycles.gen.res-eval)
    gen.res-eval
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  ?>  =(0x0 here-site)
  |-  ^-  [[sock-anno flags] gen=state]
  =*  eval-loop  $
  ~&  [here-site fol]
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  =|  =blocklist
  |-  ^-  [[sock-anno flags] state]
  =*  redo-loop  $
  =;  res
    ?-  -.res
      %&  p.res
      %|  redo-loop(blocklist (~(put ju blocklist) p.res))
    ==
  ^-  (error [[sock-anno flags] state])
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
  =.  sites.evals.gen  (~(put by sites.evals.gen) here-site sock.sub fol)
  =.  calls.evals.gen  (~(add ja calls.evals.gen) fol here-site sock.sub)
  ::  check memo cache
  ::
  ?^  m=(memo here-site fol sub gen)
    %-  (slog [(rap 3 '<1 ' (scot %ux here-site) ' <- ' (scot %ux from.u.m) ~)]~)
    &+[[pro.u.m deff] gen.u.m]
  =.  list.stack  [[sock.sub fol here-site] list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sock.sub here-site)
  =^  [code=nomm prod=sock-anno =flags]  gen
    %-  (slog [(rap 3 '>> ' (scot %ux here-site) ~)]~)
    |-  ^-  [[nomm sock-anno flags] state]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] dunno deff] gen]
        [p=^ q=^]
      =^  [l-code=nomm l-prod=sock-anno l-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [r-code=nomm r-prod=sock-anno r-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [l-code r-code]
        :+  (~(knit so sock.l-prod) sock.r-prod)
          (cons:source src.l-prod src.r-prod)
        (cons:took tok.l-prod tok.r-prod)
      (fold-flag l-flags r-flags ~)
    ::
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol dunno deff] gen]
      :_  gen
      :+  fol
        :+  (~(pull so sock.sub) p.fol)
          (slot:source src.sub p.fol)
        (slot:took tok.sub p.fol)
      deff
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol ~ ~] deff]
    ::
        [%2 p=^ q=^]
      =^  [s-code=nomm s-prod=sock-anno s-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol q.fol)
      =^  there-site  gen  [site.gen gen(site +(site.gen))]
      ?.  =(& cape.sock.f-prod)
        ::  indirect call
        ::
        %-  (slog ~[(rap 3 '<4 ' (scot %ux there-site) ~)])
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [| |] ~)
      ::  direct call
      ::
      =/  fol-new  data.sock.f-prod
      =/  fol-want=urge  (want:source src.f-prod &)
      =.  want.gen
        %-  (~(uno by want.gen) fol-want)
        |=  [@uxsite a=cape b=cape]
        ~(cut ca (~(uni ca a) b))
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
      ::  stack filtered by formula
      ::
      =/  tak  (~(get ja fols.stack) fol-new)
      |-  ^-  [[nomm sock-anno flags] state]
      =*  stack-loop  $
      ?^  tak
        ::  loop heuristic:
        ::  equal formulas, not in the blocklist, quasi matching subjects
        ::
        ?.  ?&  !(~(has ju blocklist) q.i.tak there-site)
                (close sock.s-prod p.i.tak q.i.tak gen)
            ==
          stack-loop(tak t.tak)
        ::  draft: loop calls are rendered indirect
        ::  TODO direct loops like in orig
        ::
        %-  (slog [(rap 3 '<4 ' (scot %ux there-site) ~)]~)
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [| |] ~)
      ::  non-loop case: analyse through
      ::
      =^  [pro=sock-anno =flags]  gen
        %=  eval-loop
          sub        s-prod
          fol        fol-new
          here-site  there-site
        ==
      :_  gen
      :+  [%2 s-code f-code there-site]
        pro
      (fold-flag flags s-flags f-flags ~)
    ::
        [%3 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%3 p-code]
        dunno
      p-flags
    ::
        [%4 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%4 p-code]
        dunno
      p-flags
    ::
        [%5 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%5 p-code q-code]
        dunno
      (fold-flag p-flags q-flags ~)
    ::
        [%6 c=^ y=^ n=^]
      =^  [c-code=nomm * c-flags=flags]       gen  fol-loop(fol c.fol)
      =^  [y-code=nomm y-prod=sock-anno y-flags=flags]  gen  fol-loop(fol y.fol)
      =^  [n-code=nomm n-prod=sock-anno n-flags=flags]  gen  fol-loop(fol n.fol)
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
      (fold-flag c-flags y-flags n-flags ~)
    ::
        [%7 p=^ q=^]
      =^  [p-code=nomm p-prod=sock-anno p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm q-prod=sock-anno q-flags=flags]  gen
        fol-loop(fol q.fol, sub p-prod)
      ::
      :_  gen
      :+  [%7 p-code q-code]
        q-prod
      (fold-flag p-flags q-flags ~)
    ::
        [%8 p=^ q=^]
      fol-loop(fol [%7 [p.fol %0 1] q.fol])
    ::
        [%9 p=@ q=^]
      fol-loop(fol [%7 q.fol %2 [%0 1] %0 p.fol])
    ::
        [%10 [a=@ don=^] rec=^]
      ?:  =(0 a.fol)  [[[%0 0] dunno [| &]] gen]
      =^  [don-code=nomm don-prod=sock-anno don-flags=flags]  gen
        fol-loop(fol don.fol)
      ::
      =^  [rec-code=nomm rec-prod=sock-anno rec-flags=flags]  gen
        fol-loop(fol rec.fol)
      ::
      :_  gen
      :+  [%10 [a.fol don-code] rec-code]
        :+  (~(darn so sock.rec-prod) a.fol sock.don-prod)
          (edit:source src.rec-prod a.fol src.don-prod)
        (edit:took tok.rec-prod a.fol tok.don-prod)
      (fold-flag rec-flags don-flags ~)
    ::
        [%11 p=@ q=^]
      =^  [q-code=nomm q-prod=sock-anno q-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%s11 p.fol q-code]
        q-prod
      q-flags
    ::
        [%11 [a=@ h=^] f=^]
      ::
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol f.fol)
      =^  [h-code=nomm h-prod=sock-anno h-flags=flags]  gen  fol-loop(fol h.fol)
      :_  gen
      :+  [%d11 [a.fol h-code] f-code]
        f-prod
      (fold-flag f-flags h-flags ~)
    ::
        [%12 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      [[[%12 p-code q-code] dunno (fold-flag p-flags q-flags ~)] gen]
    ==
  ::
  ::  save results
  ::
  =.  every.results.gen  (~(put by every.results.gen) here-site code prod)
  ::  if finalized: update loopiness (caller is not loopy due to a call to
  ::  a finalized entry into a cycle)
  ::
  =;  fin=(error [loopy=? gen=state])
    ?:  ?=(%| -.fin)  fin
    &+[[prod flags(loopy loopy.p.fin)] gen.p.fin]
  ?.  loopy.flags  &+[| (final-simple here-site code prod gen direct.flags)]
  =*  i  i.-.cycles.gen
  ?.  =(here-site entry.i)  &+[& (process here-site prod gen direct.flags)]
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  (final-cycle here-site prod frond.i gen direct.flags)
::  finalize analysis of non-loopy formula
::
++  final-simple
  |=  [site=@uxsite code=nomm prod=sock-anno gen=state direct=?]
  ^-  state
  %-  (slog [(rap 3 '>3 ' (scot %ux site) ~)]~)
  ::  memoize if fully direct
  ::
  =?  memo.results.gen  direct
    =/  want-site=cape  (~(gut by want.gen) site |)
    =/  want-res=urge  (want:source src.prod cape.sock.prod)
    =/  mask=cape  :: XX push mask to want.gen? original doesn't do it, but why?
      %-  ~(uni ca want-site)
      (~(gut by want-res) site |)
    ::
    %-  ~(put by memo.results.gen)
    :+  site  code
    :_  want-site
    :+  ~(norm so (~(app ca mask) sock.prod))
      (mask:source src.prod mask)
    tok.prod
  ::
  gen
::  finalize analysis of a call graph cycle entry: pop cycle, verify assumptions
::
++  final-cycle
  |=  [site=@uxsite prod=sock-anno =frond gen=state direct=?]
  ^-  err-state
  stub
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  [site=@uxsite prod=sock-anno gen=state direct=?]
  ^-  state
  stub
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state]
  ^-  (unit [from=@uxsite pro=sock-anno gen=state])
  :: ~
  =/  calls  (~(get ja calls.evals.gen) fol)
  |-  ^-  (unit [@uxsite sock-anno state])
  ?~  calls  ~
  ?~  res=(~(get by memo.results.gen) site.i.calls)  $(calls t.calls)
  ?.  (~(huge so sock.prod.u.res) sock.sub)          $(calls t.calls)
  =/  sub-want  (want:source src.sub want.u.res)
  =.  want.gen
    %-  (~(uno by want.gen) sub-want)
    |=  [@uxsite a=cape b=cape]
    ~(cut ca (~(uni ca a) b))
  ::
  =.  every.results.gen  (~(put by every.results.gen) site [nomm prod]:u.res)
  :-  ~
  :-  site.i.calls
  :_  gen
  :+  (relo-sock:took sock.sub sock.prod.u.res tok.prod.u.res)
    (relo-src:took src.sub src.prod.u.res tok.prod.u.res)
  tok.prod.u.res
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=state]
  ^-  ?
  =/  par-want=cape  (~(gut by want.gen) par-site |)
  =/  par-mask=sock  (~(app ca par-want) par-sub)
  (~(huge so par-mask) kid-sub)
::  fold flags of children expressions
::
++  fold-flag
  |=  l=(lest flags)
  ^-  flags
  =/  out=flags  i.l
  %+  roll  t.l
  |:  [f=*flags out=out]
  [|(loopy.f loopy.out) &(direct.f direct.out)]
::
++  run-nomm
  |=  [s=* f=*]
  ^-  (unit)
  =/  gen  (scan s f)
  =/  n=nomm  nomm:(~(got by every.results.gen) 0x0)
  |-  ^-  (unit)
  ?-    n
      [p=^ q=*]
    =/  l  $(n p.n)
    ?~  l  ~
    =/  r  $(n q.n)
    ?~  r  ~
    `[u.l u.r]
  ::
      [%0 p=@]
    ?:  =(0 p.n)  ~&  '[%0 0]'  ~
    ?:  =(1 p.n)  `s
    =-  ~?  ?=(~ -)  '%0 crash'  -
    (mole |.(.*(s [0 p.n])))
  ::
      [%1 p=*]
    `p.n
  ::
      [%2 *]
    =/  s1  $(n p.n)
    ?~  s1  ~
    =/  f1  $(n q.n)
    ?~  f1  ~
    ?~  call=(~(get by sites.evals.gen) site.n)
      ~&  %indirect
      (run-nomm u.s1 u.f1)
    ?.  (~(huge so sub.u.call) & u.s1)
      ~|  site.n
      ~|  [need+sub.u.call got+[& u.s1]]
      !!
    =/  res  (~(got by every.results.gen) site.n)
    $(s u.s1, n nomm.res)
  ::
      [%3 *]
    =/  p  $(n p.n)
    ?~  p  ~
    `.?(u.p)
  ::
      [%4 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?^  u.p  ~&  '%4 cell'  ~
    `+(u.p)
  ::
      [%5 *]
    =/  p  $(n p.n)
    ?~  p  ~
    =/  q  $(n q.n)
    ?~  q  ~
    `=(u.p u.q)
  ::
      [%6 *]
    =/  p  $(n p.n)
    ?~  p  ~
    ?+  u.p  ~&('%6 non-loobean' ~)
      %&  $(n q.n)
      %|  $(n r.n)
    ==
  ::
      [%7 *]
    =/  p  $(n p.n)
    ?~  p  ~
    $(s u.p, n q.n)
  ::
      [%10 *]
    ?:  =(0 p.p.n)  ~&  '%10 0'  ~
    =/  don  $(n q.p.n)
    ?~  don  ~
    =/  rec  $(n q.n)
    ?~  rec  ~
    =-  ~?  ?=(~ -)  '%10 crash'  -
    (mole |.(.*([u.don u.rec] [%10 [p.p.n %0 2] %0 3])))
  ::
      [%s11 *]
    $(n q.n)
  ::
      [%d11 *]
    =/  h  $(n q.p.n)
    ?~  h  ~
    $(n q.n)
  ::
      [%12 *]
    ~|  %no-scry  !!
  ==
--