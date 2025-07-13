/-  *noir
/+  hoot
/+  playpen
::    
=*  stub  !!
=*  one  `@`1
::  ignorant sock-anno
::
=/  dunno  [|+~ ~]
::  default flags: not loopy, fully direct
::
=/  deff  [| &]
::  Wing for compile-time branching in printing routines
::
=/  verb  ~
::  print bars?
::
=/  p-bars  &
::  print filename?
::
=/  p-file  |
::
|%
++  uni-melo
  |=  l=(list (jar * meal))
  ^-  (jar * (pair @ meal))
  ~+
  =>  !@(verb ~&(>> %uni-melo-recalc .) .)
  ?~  l  ~
  =/  out=(jar * (pair @ meal))
    %-  ~(run by i.l)
    |=  l=(list meal)
    (turn l (lead 0))
  ::
  =/  c  1
  =/  rest  t.l
  |-  ^+  out
  ?~  rest  out
  =/  next=(jar * (pair @ meal))
    %-  ~(run by i.l)
    |=  l=(list meal)
    (turn l (lead c))
  ::
  =.  out
    %-  (~(uno by out) next)
    |=  [* ls=[(list [@ meal]) (list [@ meal])]]
    (weld ls)
  ::
  $(c +(c), rest t.rest)
::
++  weld-meal
  |=  [* ls=[(list meal) (list meal)]]
  (weld ls)
::
++  scux  ^~((cury scot %ux))
::  print analysis stack
::
++  p
  |%
  ++  print
    |=  [bars=@ud tag=cord comment=tank diff=@s]
    ^+  bars
    ?.  p-bars  ((slog [%rose [~ ~ ~] tag ': ' comment ~]~) 0)
    =/  [bars-print=@ bars-return=@]
      ?+  diff  ~|(%weird-diff !!)
        %--0  [bars bars]
        %--1  [. .]:(succ bars)
        %-1   [bars ~|(%bars-underrun (dec bars))]
      ==
    ::
    %.  bars-return
    %-  slog
    :_  ~
    [%rose [~ ~ ~] tag ': ' leaf+(reap bars-print '|') ' ' comment ~]
  ::
  ++  ren
    |=  pot=spot
    ^-  tank
    =/  loc=tank
      =*  l   p.q.pot
      =*  r   q.q.pot
      =/  ud  |=(a=@u (scow %ud a))
      leaf+"<[{(ud p.l)} {(ud q.l)}].[{(ud p.r)} {(ud q.r)}]>"
    ::
    ?.  p-file  loc
    [%rose [":" ~ ~] (smyt p.pot) loc ~]
  ::
  ++  step
    |=  [site=@uxsite seat=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'step' - --1)
    ^-  tank
    ?~  seat  (scux site)
    [%rose [" " ~ ~] (scux site) (ren u.seat) ~]
  ::
  ++  loop
    |=  $:  kid=@uxsite
            par=@uxsite
            kid-seat=(unit spot)
            par-area=(unit spot)
            bars=@ud
        ==
    ^+  bars
    =-  (print bars 'loop' - --0)
    ^-  tank
    ?:  |(?=(~ kid-seat) ?=(~ par-area))
      [%rose [" =?= " ~ ~] (scux kid) (scux par) ~]
    :+  %rose  ["; " ~ ~]
    :~
      [%rose [" =?= " ~ ~] ~[(scux kid) (scux par)]]
      [%rose [" =?> " ~ ~] (ren u.kid-seat) (ren u.par-area) ~]
    ==
  ::
  ++  done
    |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'done' - -1)
    ^-  tank
    ?~  area  (scux site)
    :+  %rose  ["; " ~ ~]
    :~
      (scux site)
      [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
    ==
  ::
  ++  indi
    |=  [site=@uxsite seat=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'indi' - --0)
    ^-  tank
    ?~  seat  (scux site)
    [%rose ["; " ~ ~] (scux site) (ren u.seat) ~]
  ::
  ++  fini
    |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'fini' - -1)
    ^-  tank
    ?~  area  (scux site)
    :+  %rose  ["; " ~ ~]
    :~
      (scux site)
      [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
    ==
  ::
  ++  ciao
    |=  [site=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'ciao' - -1)
    ^-  tank
    ?~  area  (scux site)
    :+  %rose  ["; " ~ ~]
    :~
      (scux site)
      [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
    ==
  ::
  ++  memo
    |=  [here=@uxsite from=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'memo' - --0)
    ^-  tank
    ?~  area
      [%rose [" === " ~ ~] (scux here) (scux from) ~]
    :+  %rose  ["; " ~ ~]
    :~
      [%rose [" === " ~ ~] (scux here) (scux from) ~]
      [%rose [" ==> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
    ==
  ::
  ++  melo
    |=  [here=@uxsite from=@uxsite seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'melo' - --0)
    ^-  tank
    ?~  area
      [%rose [" =?= " ~ ~] (scux here) (scux from) ~]
    :+  %rose  ["; " ~ ~]
    :~
      [%rose [" =?= " ~ ~] (scux here) (scux from) ~]
      [%rose [" =?> " ~ ~] ?~(seat '??' (ren u.seat)) (ren u.area) ~]
    ==
  --
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
::  error: either m or parent-kid assumption pair which turned out to be false
::
++  error
  |$  [m]
  (each m (trel ?(%loop %melo) @uxsite @uxsite))
::
+$  err-state  (error state)
+$  frond  (deep [par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock-anno])
+$  cycle
  $:  entry=@uxsite
      latch=@uxsite
      =frond
      set=(deep @uxsite)
      melo=(jar * meal)
      hits=(deep [new=@uxsite new-sub=sock-anno =meal])
  ==
::
++  add-frond
  |=  [new=[par=@uxsite kid=@uxsite sock sock-anno] cycles=(list cycle)]
  ^-  (list cycle)
  ?:  |(?=(~ cycles) (gth par.new latch.i.cycles))
    ::  push new cycle
    ::
    :_  cycles
    ^-  cycle
    [par.new kid.new [%list new ~] [%list ~[kid.new]] ~ list+~]
  ::  pop and extend top cycle
  ::
  =/  new-cycle=cycle
    :*  (min par.new entry.i.cycles)
        kid.new
        (dive frond.i.cycles new)
        (dive set.i.cycles kid.new)
        melo.i.cycles
        hits.i.cycles
    ==
  ::
  =/  rest  t.cycles
  ::
  |-  ^-  (list cycle)
  ?:  |(?=(~ rest) (gth entry.new-cycle latch.i.rest))
    ::  push extended cycle
    ::
    [new-cycle rest]
  ::  pop and merge overlapping cycle
  ::
  =.  entry.new-cycle  (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle  [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle    [%deep set.new-cycle set.i.rest]
  =.  melo.new-cycle   ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle   [%deep hits.new-cycle hits.i.rest]
  ::
  $(rest t.rest)
::
+$  state
  ::  global state
  ::    results:  result table
  ::    site:     eval index generator
  ::    cycles:   stack of call graph cycles (aka natural loops aka strongly
  ::    connected components)
  ::      entry: top-most entry into a cyclical call graph
  ::      latch: right-most, bottom-most evalsite of the cycle
  ::      frond: set of parent-kid pairs of loop assumptions
  ::             (target of hypothetical backedge, target of the actual edge,
  ::              subject socks at the par/kid evalsites)
  ::      set: set of all vertices in the cycle (to delete from want.gen when
  ::           done)
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
  ::      merging if new cycle overlaps with the predecessor
  ::      (new entry <= previous latch)
  ::
  ::    want: evalsite subject requirements of non-finalized evalsites:
  ::      parts of the subject that are used as code
  ::
  $:  =results
      site=@uxsite
      cycles=(list cycle)
      want=urge
      bars=@ud
      block-loop=blocklist
      block-melo=blocklist
      area=(unit spot)
  ==
::
+$  stack
  ::  TODO leave essential
  ::
  $:
    ::  list: linear stack of evalsites
    ::    
    list=(list (trel sock * @uxsite))
    ::  fols: search by formula
    ::
    fols=(jar * (pair sock-anno @uxsite))
    ::  set: set of evalsites on the stack
    ::
    set=(set @uxsite)
    areas=(map @uxsite spot)
  ==
::
++  scan
  |=  [bus=* fol=*]  :: no autocons disassembly
  ^-  state
  =|  gen=state
  =|  =stack  ::  lexically scoped
  =/  sub=sock-anno  [&+bus ~]
  =;  res-eval
    ::  debug asserts
    ::
    ?>  =(~ cycles.gen.res-eval)
    ?.  =(~ want.gen.res-eval)
      ~|  ~(key by want.gen.res-eval)
      !!
    gen.res-eval
  =^  here-site  gen  [site.gen gen(site +(site.gen))]
  =|  seat=(unit spot)  ::  call site
  |-  ^-  [[sock-anno flags] gen=state]
  =*  eval-loop  $
  =|  trace=(list spot)
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  |-  ^-  [[sock-anno flags] state]
  =*  redo-loop  $
  =;  res
    ?-  -.res
      %&  p.res
      %|  =>  !@(verb ~&(>>> [%redo res] .) .)
          ?-    p.p.res
              %loop
            redo-loop(block-loop.gen (~(put ju block-loop.gen) q.p.res r.p.res))
          ::
              %melo
            redo-loop(block-melo.gen (~(put ju block-melo.gen) q.p.res r.p.res))
          ::
    ==    ==
  ^-  (error [[sock-anno flags] state])
  ::  record current evalsite in the subject provenance tree
  ::
  =.  src.sub
    ?~  src.sub  [[one here-site]~ ~ ~]
    src.sub(n [[one here-site] n.src.sub])
  ::  check memo cache
  ::
  ?^  m=(memo here-site fol sub gen set.stack)
    =>  !@  verb
          %=    .
              bars.gen.u.m
            (memo:p here-site from.u.m seat area.u.m bars.gen.u.m)
          ==
        .
    =.  src.pro.u.m  (mask:source src.pro.u.m cape.sock.pro.u.m `set.stack)
    &+[[pro.u.m deff] gen.u.m]
  ::  check melo cache (melo hit makes call loopy, might merge some cycles)
  ::
  ?^  m=(melo here-site fol sub gen set.stack)
    =>  !@  verb
          %=    .
              bars.gen.u.m
            (melo:p here-site from.u.m seat area.u.m bars.gen.u.m)
          ==
        .
    =.  src.pro.u.m  (mask:source src.pro.u.m cape.sock.pro.u.m `set.stack)
    &+[[pro.u.m [& &]] gen.u.m]
  ::
  ::  push on the stack
  ::
  =.  set.stack   (~(put in set.stack) here-site)
  ::  XX excessive masking throughout? invariant: only provenance from above
  ::
  =.  src.sub  (mask:source src.sub cape.sock.sub `set.stack)
  ::
  =.  list.stack  [[sock.sub fol here-site] list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sub here-site)
  ::
  =^  [code=nomm prod=sock-anno =flags]  gen
    =>  !@(verb .(bars.gen (step:p here-site seat bars.gen)) .)
    |-  ^-  [[nomm sock-anno flags] state]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] dunno deff] gen]
        [p=^ q=^]
      =^  [l-code=nomm l-prod=sock-anno l-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [r-code=nomm r-prod=sock-anno r-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [l-code r-code]
        :-  (~(knit so sock.l-prod) sock.r-prod)
        (cons:source src.l-prod src.r-prod)
      (fold-flag l-flags r-flags ~)
    ::
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol dunno deff] gen]
      :_  gen
      :+  fol
        :-  (~(pull so sock.sub) p.fol)
        (slot:source src.sub p.fol)
      deff
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol ~] deff]
    ::
        [%2 p=^ q=^]
      =^  [s-code=nomm s-prod=sock-anno s-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol q.fol)
      =^  there-site  gen  [site.gen gen(site +(site.gen))]
      ?.  =(& cape.sock.f-prod)
        ::  indirect call
        ::
        =>  !@  verb
              .(bars.gen (indi:p there-site ?~(trace ~ `i.trace) bars.gen))
            .
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [| |] ~)
      ::  direct call
      ::
      =/  fol-new  data.sock.f-prod
      =/  fol-urge  (urge:source (mask:source src.f-prod & `set.stack) &)
      =.  want.gen  (uni-urge:source want.gen fol-urge)
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
        ?:  (~(has ju block-loop.gen) q.i.tak there-site)
          stack-loop(tak t.tak)
        ?~  want=(close sock.s-prod sock.p.i.tak q.i.tak gen)
          stack-loop(tak t.tak)
        ::  loop hit
        ::
        ::  CAREFUL: ackchyually, here-site is the backedge root,
        ::  there-site/q.i.tak are the backedge targets that are assumed to be
        ::  the same (kid/parent) (but it should be totally fine to use kid as
        ::  latch, since we don't analyse through kid and all other calls that
        ::  would be greater than the latch would also be greater than the kid,
        ::  and vice versa)
        ::
        =>  !@  verb
              %=    .
                  bars.gen
                =/  kid-seat  ?~(trace ~ `i.trace)
                =/  par-area=(unit spot)
                  ?:  =(q.i.tak here-site)  area.gen
                  (~(get by areas.stack) q.i.tak)
                ::
                (loop:p there-site q.i.tak kid-seat par-area bars.gen)
              ==
            .
        =.  cycles.gen
          (add-frond [q.i.tak there-site sock.p.i.tak s-prod] cycles.gen)
        ::
        :_  gen
        :+  [%2 s-code f-code there-site]
          dunno
        (fold-flag s-flags f-flags [& &] ~)
      ::  non-loop case: analyse through
      ::
      =/  area-stash  area.gen
      =^  [pro=sock-anno =flags]  gen
        %=  eval-loop
          sub          s-prod
          fol          fol-new
          here-site    there-site
          seat         ?~(trace ~ `i.trace)
          area.gen     ~
          areas.stack  ?~  area.gen  areas.stack
                       (~(put by areas.stack) here-site u.area.gen)
        ==
      :_  gen(area area-stash)
      :+  [%2 s-code f-code there-site]
        =.  src.pro  (mask:source src.pro cape.sock.pro `set.stack)
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
      =^  [c-code=nomm * c-flags=flags]                 gen  fol-loop(fol c.fol)
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
        :-  int-sock
        ::  mask unified provenance tree with intersection cape
        ::
        (mask:source uni-source cape.int-sock `set.stack)
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
        :-  (~(darn so sock.rec-prod) a.fol sock.don-prod)
        (edit:source src.rec-prod a.fol src.don-prod)
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
      =^  [h-code=nomm h-prod=sock-anno h-flags=flags]  gen  fol-loop(fol h.fol)
      =>  !@  verb
            =/  pot=(unit spot)
              ?.  =(%spot a.fol)  ~
              ((soft spot) data.sock.h-prod)
            ::
            ?~  pot  +
            %_  +
              area.gen  ?~(area.gen pot area.gen)
              trace  [u.pot trace]
            ==
          .
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol f.fol)
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
  ::  prune provenance tree to leave only calls on the stack (ourselves
  ::  included), removing cousin provenance; also mask down to the product cape
  ::
  =.  src.prod  (mask:source src.prod cape.sock.prod `set.stack)
  ?.  (check:source src.prod here-site)
    ~|  src.prod
    ~|  here-site
    !!
  =;  fin=(error [loopy=? gen=state])
    ?:  ?=(%| -.fin)  fin
    &+[[prod flags(loopy loopy.p.fin)] gen.p.fin]
  ?.  loopy.flags
    ::  success, non-loopy
    ::
    :+  %&  %|
    (final-simple here-site sub fol code prod gen direct.flags seat)
  ?~  cycles.gen  !!
  ?.  =(here-site entry.i.cycles.gen)
    &+[& (process here-site sub fol code prod gen seat)]
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  ^-  err-state
  (final-cycle here-site sub fol code prod gen direct.flags seat)
::  finalize analysis of non-loopy formula
::
++  final-simple
  |=  $:  site=@uxsite
          sub=sock-anno
          fol=*
          code=nomm
          prod=sock-anno
          gen=state
          direct=?
          seat=(unit spot)
      ==
  ^-  state
  =>  !@(verb .(bars.gen (done:p site seat area.gen bars.gen)) .)
  =/  mayb-site=(unit cape)  (~(get by want.gen) site)
  =/  want-site=cape  ?~(mayb-site | u.mayb-site)
  ::  minified subject for codegen
  ::
  =/  less-code=sock  (~(app ca want-site) sock.sub)
  ::  we start off with more knowledge in the subject and mask down, 
  ::  so the intersection of want-site and cape.sock.sub should be exactly
  ::  equal to want-site?
  ::
  ?.  =(want-site cape.less-code)
    ~_  'cape.less-code < want-site'
    ~|  [cape.less-code want-site]
    !!
  =.  final.results.gen  (~(put by final.results.gen) site less-code code)
  =?  memo.results.gen  direct
    =/  capture-res=cape
      (~(gut by (urge:source src.prod cape.sock.prod)) site |)
    ::  unify +route:source and getting capture-res?
    ::
    =/  map  (route:source src.prod site)
    =/  mask=cape  (~(uni ca want-site) capture-res)
    =/  less-memo  (~(app ca mask) sock.sub)
    ?.  =(mask cape.less-memo)
      ~_  'cape.less-memo < mask'
      ~|  [cape.less-memo mask]
      !!
    %+  ~(add ja memo.results.gen)  fol
    :*  site
        code
        ::  minimized subjects' socks for memo checks and code checks
        ::
        less-memo
        less-code
        ::  full result, captured subject was included in memo requirement
        ::
        sock.prod
        map
        area.gen
    ==
  ::
  =?  want.gen  ?=(^ mayb-site)  (~(del by want.gen) site)
  gen
::  given that b > a, for each axis that used to be %.n in a and became not that
::  in b, what subaxes are set to %.y?
::
++  dif-ca
  |=  [a=cape b=cape]
  ^-  (list (trel @ @ (lest @)))
  =/  rev  1
  |-  ^-  (list (trel @ @ (lest @)))
  ?:  ?=(%& a)  ~
  ?:  ?=(%| a)
    ?~  yea=~(yea ca b)  ~
    ~[[(xeb rev) rev yea]]
  %:  weld
    $(a -.a, b ?@(b b -.b), rev (peg rev 2))
    $(a +.a, b ?@(b b +.b), rev (peg rev 3))
  ==
::  (~(huge so a) b) failed, what are the offending subsocks?
::
++  dif-so
  |=  [a=sock b=sock]
  ^-  (list (pair @ (lest (pair @ ?(%lost %data)))))
  =*  res  ,(list (pair @ (lest (pair @ ?(%lost %data)))))
  =/  rev  1
  |-  ^-  res
  ?:  |(?=(^ cape.a) ?=(^ cape.b))
    %:  weld
      $(a ~(hed so a), b ~(hed so b), rev (peg rev 2))
      $(a ~(tel so a), b ~(tel so b), rev (peg rev 3))
    ==
  ?:  ?=(%| cape.a)  ~
  ?:  ?=(%| cape.b)  ~[[rev ~[[1 %lost]]]]
  =/  rel  1
  =-  ?~  -  ~  ~[[rev -]]
  |-  ^-  (list (pair @ ?(%lost %data)))
  ?:  =(data.a data.b)  ~
  ?.  &(?=(^ data.a) ?=(^ data.b))  ~[[rel %data]]
  %:  weld
    $(data.a -.data.a, data.b -.data.b, rel (peg rel 2))
    $(data.a +.data.a, data.b +.data.b, rel (peg rel 3))
  ==
::
++  max-xeb-ax
  |=  n=*
  ^-  @
  =/  rev  1
  |-  ^-  @
  ?@  n  (xeb rev)
  (max $(n -.n, rev (peg rev 2)) $(n +.n, rev (peg rev 3)))
::  finalize analysis of a call graph cycle entry: pop cycle, verify assumptions
::
++  final-cycle
  |=  $:  site=@uxsite
          sub=sock-anno
          fol=*
          code=nomm
          prod=sock-anno
          gen=state
          direct=?
          seat=(unit spot)
      ==
  ^-  err-state
  =.  process.results.gen  (~(put by process.results.gen) site code sock.sub)
  =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
  ::  validate fronds
  ::
  =/  err-gen=err-state
    %+  reel-deep  frond.pop
    |:  :-  *[par=@uxsite kid=@uxsite par-sub=sock kid-sub=sock-anno]
        err-gen=`err-state`&+gen
    ^-  err-state
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =^  par-final=sock  gen
      =.  src.kid-sub  (mask:source src.kid-sub cape.sock.kid-sub ~)
      =/  c  0
      ::
      =/  par-want-1=cape  (~(gut by want.gen) par |)
      =/  par-masked-1=sock  (~(app ca par-want-1) par-sub)
      |-  ^-  [sock state]
      =/  kid-sub-urge  (urge:source src.kid-sub par-want-1)
      =.  want.gen  (uni-urge:source want.gen kid-sub-urge)
      =/  par-want-2=cape  (~(gut by want.gen) par |)
      =/  par-masked-2=sock  (~(app ca par-want-2) par-sub)
      ?:  =(~(norm so par-masked-1) ~(norm so par-masked-2))
        [par-masked-1 gen]
      =>  !@(verb ~&(>> fixpoint-loop+c .) .)
      $(par-masked-1 par-masked-2, c +(c), par-want-1 par-want-2)
    ::
    ?.  (~(huge so par-final) sock.kid-sub)  |+[%loop par kid]
    =.  process.results.gen
      %+  ~(put by process.results.gen)  kid
      (~(got by process.results.gen) par)
    ::
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  ::  remove err-gen
  ::
  =>  +
  ::  validate melo hits
  ::
  =/  err-gen=err-state
    %+  reel-deep  hits.pop
    |:  :-  ^*  $:  new=@uxsite
                    new-sub=sock-anno
                    old=@uxsite
                    code=nomm
                    capture=cape
                    old-sub=sock-anno
                    *
                ==
        err-gen=`err-state`&+gen
    ^-  err-state
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =^  old-final=sock  gen
      =.  src.new-sub  (mask:source src.new-sub cape.sock.new-sub ~)
      =/  old-want-1=cape  (~(gut by want.gen) old |)
      =/  old-masked-1=sock  (~(app ca old-want-1) sock.old-sub)
      |-  ^-  [sock state]
      =/  new-sub-urge  (urge:source src.new-sub old-want-1)
      =.  want.gen  (uni-urge:source want.gen new-sub-urge)
      =/  old-want-2=cape  (~(gut by want.gen) old |)
      =/  old-masked-2=sock  (~(app ca old-want-2) sock.old-sub)
      ?:  =(~(norm so old-masked-1) ~(norm so old-masked-2))
        [old-masked-1 gen]
      ~&  >>  %fixpoint-melo
      $(old-masked-1 old-masked-2, old-want-1 old-want-2)
    ::
    ?.  (~(huge so old-final) sock.new-sub)  |+[%melo old new]
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  =>  +
  =>  !@(verb .(bars.gen (fini:p site seat area.gen bars.gen)) .)
  =/  want-site=cape  (~(gut by want.gen) site |)
  =/  less-code=sock  (~(app ca want-site) sock.sub)
  ?.  =(want-site cape.less-code)
    ~_  'cape.less-code < want-site'
    ~|  [cape.less-code want-site]
    !!
  =.  final.results.gen  (~(put by final.results.gen) site less-code code)
  =.  final.results.gen
    %+  roll-deep  set.pop
    |:  [site=*@uxsite final=final.results.gen]
    ^+  final
    =/  proc  (~(got by process.results.gen) site)
    =/  want-site=cape  (~(gut by want.gen) site |)
    =/  less-code=sock  (~(app ca want-site) sub.proc)
    ?.  =(want-site cape.less-code)
      ~_  'cape.less-code < want-site'
      ~|  [cape.less-code want-site]
      !!
    (~(put by final) site less-code nomm.proc)
  ::
  =?  memo.results.gen  direct
    =/  capture-res=cape
      (~(gut by (urge:source src.prod cape.sock.prod)) site |)
    ::
    =/  map  (route:source src.prod site)
    =/  less-memo=sock
      =/  mask=cape  (~(uni ca want-site) capture-res)
      =/  less  (~(app ca mask) sock.sub)
      ?.  =(mask cape.less)
        ~_  'cape.less < mask'
        ~|  [cape.less mask]
        !!
      less
    ::
    %+  ~(add ja memo.results.gen)  fol
    :*  site
        code
        less-memo
        less-code
        sock.prod
        map
        area.gen
    ==
  ::
  =.  want.gen  (~(del by want.gen) site)
  =.  want.gen
    %+  roll-deep  set.pop
    |:  [v=*@uxsite acc=want.gen]
    (~(del by acc) v)
  ::
  &+gen
::  treat analysis result of a non-finalized evalsite
::
++  process
  |=  $:  site=@uxsite
          sub=sock-anno
          fol=*
          code=nomm
          prod=sock-anno
          gen=state
          seat=(unit spot)
      ==
  ^-  state
  =>  !@(verb .(bars.gen (ciao:p site seat area.gen bars.gen)) .)
  ?~  cycles.gen  !!
  =.  set.i.cycles.gen   (dive set.i.cycles.gen site)
  =/  capture-res=cape
    (~(gut by (urge:source src.prod cape.sock.prod)) site |)
  ::
  =/  map  (route:source src.prod site)
  =.  melo.i.cycles.gen
    %+  ~(add ja melo.i.cycles.gen)  fol
    :*  site
        code
        capture-res
        sub
        sock.prod
        map
        area.gen
    ==
  ::
  =.  process.results.gen  (~(put by process.results.gen) site code sock.sub)
  gen
::
++  memo
  |=  [site=@uxsite fol=* sub=sock-anno gen=state stack=(set @uxsite)]
  ^-  (unit [from=@uxsite area=(unit spot) pro=sock-anno gen=state])
  =/  meme  (~(get ja memo.results.gen) fol)
  |-  ^-  (unit [@uxsite (unit spot) sock-anno state])
  ?~  meme  ~
  =*  i  i.meme
  ?.  (~(huge so less-memo.i) sock.sub)  $(meme t.meme)
  ::  memo hit: propagate subject needs
  :: 
  =/  sub-urge
    (urge:source (mask:source src.sub cape.sock.sub `stack) cape.less-code.i)
  ::
  =.  want.gen  (uni-urge:source want.gen sub-urge)
  =.  final.results.gen
    (~(put by final.results.gen) site less-code.i nomm.i)
  ::
  =/  src  (relo:source src.sub map.i)
  `[site.i area.i [prod.i src] gen]
::
++  melo
  |=  $:  site=@uxsite
          fol=*
          sub=sock-anno
          gen=state
          stack=(set @uxsite)
      ==
  ^-  (unit [from=@uxsite area=(unit spot) pro=sock-anno gen=state])
  ?:  =(~ cycles.gen)  ~
  =*  hit  ,[new=@uxsite new-sub=sock-anno =meal]
  =*  res  ,(unit [out=[@uxsite (unit spot) sock-anno gen=state] =hit depth=@])
  =/  =res
    =/  melo-dep  (uni-melo (turn cycles.gen |=(cycle melo)))
    =/  mele  (~(get ja melo-dep) fol)
    |-  ^-  res
    ?~  mele  ~
    =*  i  q.i.mele
    ?:  (~(has ju block-melo.gen) site.i site)  $(mele t.mele)
    =/  want-site=cape  (~(gut by want.gen) site.i |)
    =/  mask=cape  (~(uni ca want-site) capture.i)
    =/  less  (~(app ca mask) sock.sub.i)
    ?.  (~(huge so less) sock.sub)  $(mele t.mele)
    =.  process.results.gen
      %+  ~(put by process.results.gen)  site
      (~(got by process.results.gen) site.i)
    ::
    =/  src  (relo:source src.sub map.i)
    `[[site.i area.i [prod.i src] gen] [site sub q.i.mele] p.i.mele]
  ::
  ::
  ?~  res  ~
  ::  top melo hit: no merging necessary
  ::
  ?:  =(0 depth.u.res)
    ?~  cycles.gen.out.u.res  !!
    =*  i   i.cycles.gen.out.u.res
    =.  hits.i  (dive hits.i hit.u.res)
    =.  set.i   (dive set.i site)
    =.  latch.i  site
    `out.u.res
  =/  depth  depth.u.res
  =/  gen  gen.out.u.res
  =/  new-cycle  ,.-.cycles.gen
  =/  rest  ,.+.cycles.gen
  |-
  ?:  =(0 depth)
    =.  hits.new-cycle   (dive hits.new-cycle hit.u.res)
    =.  set.new-cycle    (dive set.new-cycle site)
    =.  latch.new-cycle  site
    =.  cycles.gen  [new-cycle rest]
    `out.u.res(gen gen)
  ?~  rest  !!
  =.  entry.new-cycle  (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle  [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle    [%deep set.new-cycle set.i.rest]
  =.  melo.new-cycle   ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle   [%deep hits.new-cycle hits.i.rest]
  $(rest t.rest, depth (dec depth))
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::  returns code usage cape if compatible
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=state]
  ^-  (unit cape)
  =/  par-want=cape  (~(gut by want.gen) par-site |)
  =/  par-masked=sock  (~(app ca par-want) par-sub)
  ?.  (~(huge so par-masked) kid-sub)  ~
  `par-want
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
++  jet-simple-gate-hoot
  =/  l=(list)
    =>  hoot
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth
        lte  lth  max  min  cap  mas  peg  bex  can
        cat  cut  end  fil  hew  lsh  met  rap  rep
        rev  rig  rip  rsh  run  rut  sew  swp  xeb
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet-simple-gate-play
  =/  l=(list)
    =>  playpen
    :~  dec  add  sub  mul  div  mod  dvr  gte  gth
        lte  lth  bex  can  cat  cut  end  fil  lsh
        met  rap  rep  rev  rip  rsh  swp  xeb
    ==
  |=  [s=* f=*]
  ^-  (unit (unit))
  ?~  l  ~
  ?:  &(=(f -.i.l) =(-.s -.i.l) =(+>.s +>.i.l))
    `(mure |.((slum i.l +<.s)))
  $(l t.l)
::
++  jet
  |=  [s=* f=*]
  ^-  (unit (unit))
  :: ~
  ?^  res=(jet-simple-gate-hoot s f)  res
  ?^  res=(jet-simple-gate-play s f)  res
  ::  place for jets with nontrivial templates
  ::
  ~
::  Analyze s/f pair, then run Nomm interpreter on the result
::  Indirect calls reanalyze
::  Direct calls are verified with subject sock nest checking
::
++  run-nomm
  |=  [s=* f=*]
  ^-  (unit)
  !.
  =/  gen
    :: ~>  %bout
    (scan s f)
  =/  n  nomm:(~(got by final.results.gen) 0x0)
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
    ?~  call=(~(get by final.results.gen) site.n)
      ~&  indirect+site.n
      :: (run-nomm u.s1 u.f1)
      !!
    ?.  (~(huge so less.u.call) & u.s1)
      ~|  site.n
      :: ~|  [need+less.u.call got+[& u.s1]]
      ~|  %sock-nest-error
      !!
    ?^  res=(jet u.s1 u.f1)  u.res
    $(s u.s1, n nomm.u.call)
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