/-  *noir
/+  hoot
/+  playpen
::    
=*  stub  !!
=*  one  `@`1
::  default flags: not loopy, fully direct
::
=/  deff  [| &]
::  Wing for compile-time branching in printing routines
::
:: =/  verb  ~
::  print bars?
::
=/  p-bars  &
::  fixed width of barstack?
::
=/  f-bars  |
::  print filename?
::
=/  p-file  |
::  check that the formula does not crash, returning constant product
::
|%
::  ignorant sock-anno
::
++  dunno
  |=  sub=sock-anno
  ^-  sock-anno
  [|+~ [~[~] t.src.sub]]
  :: [|+~ [~[null+~] t.src.sub]]
::
++  safe
  |=  fol=*
  ^-  (unit *)
  ?+  fol  ~
    [%1 p=*]       `p.fol
    [%11 @ p=*]    $(fol p.fol)
    [%11 [@ h=^] p=*]  ?~(s=(safe h.fol) ~ $(fol p.fol))
  ==
::  treat %fast hint formula
::  returns ~ on failure, [~ ~] on root registration, [~ ~ @] on child
::  registration
::
++  fast-parent
  |=  fol=*
  ^-  (unit (unit @))
  ?+  fol  ~
    [%1 %0]        `~
    [%0 p=@]       ``p.fol
    [%11 @ p=*]    $(fol p.fol)
    [%11 [@ f=^] p=*]  ?~(s=(safe f.fol) ~ $(fol p.fol))
  ==
::
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
++  scuv  ^~((cury scot %uv))
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
    =/  bars=tank
      ?.  f-bars  leaf+(reap bars-print '|')
      ?:  (lte bars-print 5)  leaf+(reap bars-print '|')
      =/  num  (scow %ud bars-print)
      =/  len  (lent num)
      =?  num  (lth len 3)  (weld (reap (sub 3 len) ' ') num)
      [%rose [~ "|" "|"] leaf+num ~]
    ::
    [%rose [~ ~ ~] tag ': ' bars ' ' comment ~]
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
    |=  [seat=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'indi' - --0)
    ^-  tank
    ?~  seat  ''
    (ren u.seat)
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
    |=  [from=(pair @uvarm @uxsite) seat=(unit spot) area=(unit spot) bars=@ud]
    ^+  bars
    =-  (print bars 'memo' - --0)
    ^-  tank
    ?~  area
      [%rose ["/" ~ ~] (scuv p.from) (scux q.from) ~]
    :+  %rose  ["; " ~ ~]
    :~
      [%rose ["/" ~ ~] (scuv p.from) (scux q.from) ~]
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
  %+  each  m
  $%  [%loop p=@uxsite q=@uxsite]  ::  parent-kid
      [%melo p=@uxsite]            ::  entry of a cycle with wrong melo hit
  ==
::
+$  err-state  (error short)
::
++  add-frond
  |=  $:  new=[par=@uxsite kid=@uxsite sock sock-anno (lest @uxsite)]
          cycles=(list cycle)
      ==
  ^-  (list cycle)
  ?:  |(?=(~ cycles) (gth par.new latch.i.cycles))
    ::  push new cycle
    ::
    :_  cycles
    ^-  cycle
    [par.new kid.new [%list new ~] [%list ~[kid.new]] list+~ ~ list+~]
  ::  pop and extend top cycle
  ::
  =/  new-cycle=cycle
    :*  (min par.new entry.i.cycles)
        kid.new
        (dive frond.i.cycles new)
        (dive set.i.cycles kid.new)
        process.i.cycles
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
  =.  entry.new-cycle    (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle    [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle      [%deep set.new-cycle set.i.rest]
  =.  process.new-cycle  [%deep process.new-cycle process.i.rest]
  =.  melo.new-cycle     ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle     [%deep hits.new-cycle hits.i.rest]
  ::
  $(rest t.rest)
::
+$  stack
  ::  TODO leave essential
  ::
  $:
    ::  list: linear stack of evalsites
    ::    
    list=(list @uxsite)
    ::  fols: search by formula
    ::
    fols=(jar * (pair sock-anno @uxsite))
    ::  set: set of evalsites on the stack
    ::
    :: set=(set @uxsite)
    areas=(map @uxsite spot)
  ==
::  call info
::
+$  info  [memo=(unit @uxmemo)]
::  stateful analysis of bus/fol pair
::
++  scan
  =|  gen=short
  |=  [bus=sock fol=*]
  ^-  short
  =|  =stack  ::  lexically scoped
  ::  provenance is updated by the caller
  ::  length of the provenance list must match stack depth during analysis
  ::
  =/  sub=sock-anno  [bus ~[~[1]]]
  :: =/  sub=sock-anno  [bus ~[~[axis+1]]]
  =;  res-eval-entry=short
    ::  debug asserts
    ::
    ?>  =(~ cycles.res-eval-entry)
    ?.  =(~ want.res-eval-entry)
      ~|  ~(key by want.res-eval-entry)
      !!
    ?>  =(~ process.res-eval-entry)
    res-eval-entry
  =^  here-site  site-gen.gen  [site-gen.gen +(site-gen.gen)]
  ?>  =(0x0 here-site)
  ::  check global memo cache
  ::
  =/  meme-0  (~(get ja fols.memo.gen) fol)
  |-  ^-  short
  =*  memo-loop  $
  ?^  meme-0
    =*  i  i.meme-0
    ?.  (~(huge so less-memo.i) sock.sub)  memo-loop(meme-0 t.meme-0)
    ::  memo hit for 0x0: record entry
    ::
    =>  !@  verb
          %=    .
              bars.gen
            (memo:p [arm.i site.i] ~ area.i bars.gen)
          ==
        .
    gen(memo-entry `idx.i)
  =<  gen
  =|  seat=(unit spot)  ::  call site
  |-  ^-  [[sock-anno flags info] gen=short]
  =*  eval-loop  $
  =|  trace=(list spot)
  ::  retry evalsite analysis if a loop assumption was wrong
  ::
  |-  ^-  [[sock-anno flags info] short]
  =*  redo-loop  $
  =;  res=(error [[sock-anno flags info] short])
    ?-  -.res
      %&  p.res
      %|  =>  !@(verb ~&(>>> [%redo res] .) .)
          ?-    -.p.res
              %loop
            redo-loop(block-loop.gen (~(put ju block-loop.gen) p.p.res q.p.res))
          ::
              %melo
            redo-loop(block-melo.gen (~(put in block-melo.gen) p.p.res))
          ::
    ==    ==
  ^-  (error [[sock-anno flags info] short])
  ::  enter analysis
  ::
  ::  push on the stack
  ::
  :: =.  set.stack   (~(put in set.stack) here-site)
  =.  list.stack  [here-site list.stack]
  =.  fols.stack  (~(add ja fols.stack) fol sub here-site)
  ::
  =^  [code=nomm prod=sock-anno =flags]  gen
    =>  !@(verb .(bars.gen (step:p here-site seat bars.gen)) .)
    |-  ^-  [[nomm sock-anno flags] short]
    =*  fol-loop  $
    ?+    fol  [[[%0 0] (dunno sub) deff] gen]
        [p=^ q=^]
      =^  [l-code=nomm l-prod=sock-anno l-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [r-code=nomm r-prod=sock-anno r-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [l-code r-code]
        :-  (~(knit so sock.l-prod) sock.r-prod)
        (cons:source src.l-prod src.r-prod)
      (fold-flag l-flags r-flags ~)
    
        [%0 p=@]
      ?:  =(0 p.fol)  [[fol (dunno sub) deff] gen]
      ?:  =(1 p.fol)  [[fol sub deff] gen]
      :_  gen
      :+  fol
        :-  (~(pull so sock.sub) p.fol)
        (slot:source src.sub p.fol)
      deff
    ::
        [%1 p=*]
      :_  gen
      [fol [&+p.fol [~[~] t.src.sub]] deff]
      :: [fol [&+p.fol [~[null+~] t.src.sub]] deff]
    ::
        [%2 p=^ q=^]
      =^  [s-code=nomm s-prod=sock-anno s-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [f-code=nomm f-prod=sock-anno f-flags=flags]  gen  fol-loop(fol q.fol)
      ?.  =(& cape.sock.f-prod)
        ::  indirect call
        ::
        =>  !@  verb
              .(bars.gen (indi:p ?~(trace ~ `i.trace) bars.gen))
            .
        :_  gen
        :+  [%2 s-code f-code ~]
          (dunno sub)
        (fold-flag s-flags f-flags [| |] ~)
      ::  direct call
      ::
      =/  fol-new  data.sock.f-prod
      =/  fol-urge  (urge:source src.f-prod & ?~(list.stack !! list.stack))
      =.  want.gen  (uni-urge:source want.gen fol-urge)
      ::  check memo cache
      ::
      ?^  m=(memo fol-new s-prod gen stack)
        =>  !@  verb
              %=    .
                  bars.gen.u.m
                (memo:p from.u.m ?~(trace ~ `i.trace) area.u.m bars.gen.u.m)
              ==
            .
        :_  gen.u.m
        :+  [%2 s-code f-code memo+idx.u.m]
          pro.u.m
        (fold-flag s-flags f-flags ~)
      ::  fallible checks or analyse through: allocate new evalsite
      ::
      =^  there-site  site-gen.gen  [site-gen.gen +(site-gen.gen)]
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
      |-  ^-  [[nomm sock-anno flags] short]
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
          %+  add-frond
            [ q.i.tak
            there-site
            sock.p.i.tak
            s-prod
            ?~(list.stack !! list.stack)
            ]
          cycles.gen
        ::
        :_  gen
        :+  [%2 s-code f-code site+[here-arm.gen q.i.tak]]
          (dunno sub)
        (fold-flag s-flags f-flags [& &] ~)
      ::  check melo cache
      ::
      ?^  m=(melo there-site fol-new s-prod gen stack)
        =>  !@  verb
              %=    .
                  bars.gen.u.m
                %:  melo:p
                  there-site
                  from.u.m
                  ?~(trace ~ `i.trace)
                  area.u.m
                  bars.gen.u.m
                ==
              ==
            .
        :_  gen.u.m
        :+  [%2 s-code f-code site+[here-arm.gen from.u.m]]
          pro.u.m
        (fold-flag s-flags f-flags [& &] ~)
      ::  non-loop case: analyse through
      ::
      =/  area-stash  area.gen
      =^  [pro=sock-anno =flags =info]  gen
        %=  eval-loop
          sub          s-prod(src [~[1] src.s-prod])
          :: sub          s-prod(src [~[axis+1] src.s-prod])
          fol          fol-new
          here-site    there-site
          seat         ?~(trace ~ `i.trace)
          area.gen     ~
          areas.stack  ?~  area.gen  areas.stack
                       (~(put by areas.stack) here-site u.area.gen)
        ==
      ::
      =/  code=nomm
        :^  %2  s-code  f-code
        ?^  memo.info
          ::  the call got memoized
          ::
          memo+u.memo.info
        site+[here-arm.gen there-site]
      ::
      :_  gen(area area-stash)
      :+  code
        ?~  t.src.pro  !!
        :: ~&  (depf q.i.src.pro)
        :: ~&  (depf q.i.t.src.pro)
        %=  pro
          t.src  t.t.src.pro
          i.src  (compose:source i.src.pro i.t.src.pro)
        ==
      (fold-flag flags s-flags f-flags ~)
    ::
        [%3 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%3 p-code]
        (dunno sub)
      p-flags
    ::
        [%4 p=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      :_  gen
      :+  [%4 p-code]
        (dunno sub)
      p-flags
    ::
        [%5 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      :_  gen
      :+  [%5 p-code q-code]
        (dunno sub)
      (fold-flag p-flags q-flags ~)
    ::
        [%6 c=^ y=^ n=^]
      =^  [c-code=nomm * c-flags=flags]                 gen  fol-loop(fol c.fol)
      =^  [y-code=nomm y-prod=sock-anno y-flags=flags]  gen  fol-loop(fol y.fol)
      =^  [n-code=nomm n-prod=sock-anno n-flags=flags]  gen  fol-loop(fol n.fol)
      =/  int=sock  (~(purr so sock.y-prod) sock.n-prod)
      :_  gen
      :+  [%6 c-code y-code n-code]
        :-  int
        =,  source
        (uni (mask src.y-prod cape.int) (mask src.n-prod cape.int))
        :: (uni src.y-prod src.n-prod)
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
      ?:  =(0 a.fol)  [[[%0 0] (dunno sub) deff] gen]
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
      :_  (hint a.fol h-prod f-prod gen)
      :+  [%d11 [a.fol h-code] f-code]
        f-prod
      (fold-flag f-flags h-flags ~)
    ::
        [%12 p=^ q=^]
      =^  [p-code=nomm * p-flags=flags]  gen  fol-loop(fol p.fol)
      =^  [q-code=nomm * q-flags=flags]  gen  fol-loop(fol q.fol)
      [[[%12 p-code q-code] (dunno sub) (fold-flag p-flags q-flags ~)] gen]
    ==
  ::
  =/  move=(lest spring:source)  i.src.prod
  =/  capture=cape  (prune:source move cape.sock.prod)
  ::
  =;  fin=(error [loopy=? =info gen=short])
    ?:  ?=(%| -.fin)  fin
    &+[[prod flags(loopy loopy.p.fin) info.p.fin] gen.p.fin]
  ?.  loopy.flags
    ::  success, non-loopy
    ::
    :+  %&  %|
    ::  finalize simple
    ::
    ^-  [info short]
    =>  !@(verb .(bars.gen (done:p here-site seat area.gen bars.gen)) .)
    =/  mayb-site=(unit cape)  (~(get by want.gen) here-site)
    =/  want-site=cape  ?~(mayb-site | u.mayb-site)
    ::  minified subject for codegen
    ::
    =/  less-code=sock  (~(app ca want-site) sock.sub)
    ::  we start off with more knowledge in the subject and mask down, 
    ::  so the intersection of want-site and cape.sock.sub should be exactly
    ::  equal to want-site?
    ::
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    ::  memoize globally or save locally
    ::
    =^  =info  gen
      ?.  direct.flags
        [~ gen(locals [[here-site less-code fol code] locals.gen])]
      =^  idx  memo-gen.gen  [memo-gen.gen +(memo-gen.gen)]
      =/  mask=cape  (~(uni ca want-site) capture)
      =/  less-memo  (~(app ca mask) sock.sub)
      :: ?.  =(mask cape.less-memo)
      ::   ~_  'cape.less-memo < mask'
      ::   ~|  cape.less-memo
      ::   ~|  mask
      ::   !!
      =/  =meme
        :^  idx  here-arm.gen  here-site
        [fol code less-memo less-code sock.prod move area.gen]
      ::
      =.  fols.memo.gen  (~(add ja fols.memo.gen) fol meme)
      =.  idxs.memo.gen  (~(put by idxs.memo.gen) idx meme)
      =.  sits.memo.gen  (~(put by sits.memo.gen) [here-arm.gen here-site] meme)
      [`idx gen]
    ::
    =?  want.gen  ?=(^ mayb-site)  (~(del by want.gen) here-site)
    [info gen]
  ?~  cycles.gen  !!
  ?.  =(here-site entry.i.cycles.gen)
    ::  success, loopy
    ::
    :+  %&  %&
    ::  return without finalizing
    ::
    ^-  [info short]
    ::  never memoized
    ::
    :-  ~
    ^-  short
    =>  !@(verb .(bars.gen (ciao:p here-site seat area.gen bars.gen)) .)
    =.  set.i.cycles.gen      (dive set.i.cycles.gen here-site)
    =.  process.i.cycles.gen  (dive process.i.cycles.gen here-site)
    =.  melo.i.cycles.gen
      %+  ~(add ja melo.i.cycles.gen)  fol
      :*  here-site
          code
          capture
          sub
          sock.prod
          move
          area.gen
      ==
    ::
    =.  process.gen
      %+  ~(put by process.gen)  here-site
      [sock.sub fol code capture sock.prod move area.gen]
    ::
    gen
  ::  cycle entry not loopy if finalized
  ::
  =-  ?:  ?=(%| -<)  -  &+[| p]
  ::  attempt to finalize cycle entry
  ::
  ^-  (error (pair info short))
  =>  .(cycles.gen `(list cycle)`cycles.gen)
  =^  pop=cycle  cycles.gen  ?~(cycles.gen !! cycles.gen)
  ::  validate fronds, expanding needs
  ::
  =/  err-gen=err-state
    %+  reel-deep  frond.pop
    |:  :-  ^*
            $:  par=@uxsite
                kid=@uxsite
                par-sub=sock
                kid-sub=sock-anno
                kid-tak=(lest @uxsite)
            ==
        err-gen=`err-state`&+gen
    ^+  err-gen
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =^  par-final=sock  gen
      =/  c  0
      =/  par-want-1=cape  (~(gut by want.gen) par |)
      =/  par-masked-1=sock  (~(app ca par-want-1) par-sub)
      |-  ^-  [sock short]
      =/  kid-sub-urge  (urge:source src.kid-sub cape.par-masked-1 kid-tak)
      =.  want.gen  (uni-urge:source want.gen kid-sub-urge)
      =/  par-want-2=cape  (~(gut by want.gen) par |)
      =/  par-masked-2=sock  (~(app ca par-want-2) par-sub)
      ?:  =(cape.par-masked-1 cape.par-masked-2)
        [par-masked-1 gen]
      =>  !@(verb ~&(>> fixpoint-loop+c .) .)  ::  XX explain fixpoint search in writing
      $(par-masked-1 par-masked-2, c +(c), par-want-1 par-want-2)
    ::
    ?.  (~(huge so par-final) sock.kid-sub)  |+[%loop par kid]
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  ::  remove err-gen
  ::
  =>  +
  ::  validate melo hits, expanding what.gen
  ::
  =/  err-gen=err-state
    %+  reel-deep  hits.pop
    |:  :-  ^*  $:  new-tak=(lest @uxsite)
                    new=@uxsite
                    new-sub=sock-anno
                    old=@uxsite
                    code=nomm
                    cape  ::  melo hit validation does not require capture
                    old-sub=sock-anno
                    *
                ==
        err-gen=`err-state`&+gen
    ^-  err-state
    ?:  ?=(%| -.err-gen)  err-gen
    =/  gen  p.err-gen
    =/  old-want  (~(gut by want.gen) old |)
    =.  want.gen
      (uni-urge:source want.gen (urge:source src.new-sub old-want new-tak))
    ::
    =/  old-less  (~(app ca old-want) sock.old-sub)
    ?.  (~(huge so old-less) sock.new-sub)  |+[%melo entry.pop]
    &+gen
  ::
  ?:  ?=(%| -.err-gen)  err-gen
  =.  gen  p.err-gen
  =>  +
  =>  !@(verb .(bars.gen (fini:p here-site seat area.gen bars.gen)) .)
  ::
  ::  finalize in-process sites
  ::
  =.  gen
    %+  roll-deep  process.pop
    |:  [site=*@uxsite gen=gen]
    ^-  short
    =/  proc  (~(got by process.gen) site)
    =/  want-site=cape  (~(gut by want.gen) site |)
    =/  less-code=sock  (~(app ca want-site) sub.proc)
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    =.  locals.gen  [[site less-code fol.proc nomm.proc] locals.gen]
    =.  process.gen  (~(del by process.gen) site)
    gen
  ::  memoize or save loop entry point
  ::
  =^  =info  gen
    =/  want-site  (~(gut by want.gen) here-site |)
    =/  less-code=sock  (~(app ca want-site) sock.sub)
    :: ?.  =(want-site cape.less-code)
    ::   ~_  'cape.less-code < want-site'
    ::   ~|  cape.less-code
    ::   ~|  want-site
    ::   !!
    ?.  direct.flags
      [~ gen(locals [[here-site less-code fol code] locals.gen])]
    =^  idx  memo-gen.gen  [memo-gen.gen +(memo-gen.gen)]
    =.  memo-loop-entry.gen  [[here-site idx] memo-loop-entry.gen]
    =/  memo-mask=cape  (~(uni ca want-site) capture)
    =/  memo-less  (~(app ca memo-mask) sock.sub)
    :: ?.  =(memo-mask cape.memo-less)
    ::   ~_  'cape.less < mask'
    ::   ~|  cape.memo-less
    ::   ~|  memo-mask
    ::   !!
    =/  meme
      :^  idx  here-arm.gen  here-site
      [fol code memo-less less-code sock.prod move area.gen]
    ::
    =.  fols.memo.gen  (~(add ja fols.memo.gen) fol meme)
    =.  idxs.memo.gen  (~(put by idxs.memo.gen) idx meme)
    =.  sits.memo.gen  (~(put by sits.memo.gen) [here-arm.gen here-site] meme)
    [`idx gen]
  ::
  =.  set.pop  (dive set.pop here-site)
  =.  gen
    %+  roll-deep  set.pop
    |:  [v=*@uxsite gen=gen]
    =.  want.gen  (~(del by want.gen) v)
    gen
  ::
  &+[info gen]
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
::
++  memo
  |=  [fol=* sub=sock-anno gen=short =stack]
  ^-  %-  unit
      $:  idx=@uxmemo
          from=[@uvarm @uxsite]
          area=(unit spot)
          pro=sock-anno
          gen=short
      ==
  =/  meme  (~(get ja fols.memo.gen) fol)
  |-
  ?~  meme  ~
  =*  i  i.meme
  ?.  (~(huge so less-memo.i) sock.sub)  $(meme t.meme)
  ::  memo hit: propagate subject needs
  :: 
  =/  sub-urge
    (urge:source src.sub cape.less-code.i ?~(list.stack !! list.stack))
  ::
  =.  want.gen  (uni-urge:source want.gen sub-urge)
  =/  src  src.sub(i (compose:source map.i i.src.sub))
  `[idx.i [arm.i site.i] area.i [prod.i src] gen]
::
++  melo
  |=  $:  site=@uxsite
          fol=*
          sub=sock-anno
          gen=short
          =stack
      ==
  ^-  (unit [from=@uxsite area=(unit spot) pro=sock-anno gen=short])
  ?:  =(~ cycles.gen)  ~
  =*  hit  ,[new-tak=(lest @uxsite) new=@uxsite new-sub=sock-anno =meal]
  =*  res  ,(unit [out=[@uxsite (unit spot) sock-anno gen=short] =hit depth=@])
  =/  =res
    =/  melo-dep  (uni-melo (turn cycles.gen |=(cycle melo)))
    =/  mele  (~(get ja melo-dep) fol)
    |-  ^-  res
    ?~  mele  ~
    =*  i  q.i.mele
    :: ?:  (~(has ju block-melo.gen) site.i site)  $(mele t.mele)
    =/  want-site=cape  (~(gut by want.gen) site.i |)
    =/  mask=cape  (~(uni ca want-site) capture.i)
    =/  less  (~(app ca mask) sock.sub.i)
    ?.  (~(huge so less) sock.sub)  $(mele t.mele)
    =/  src  src.sub(i (compose:source map.i i.src.sub))
    =/  tak  ?~(list.stack !! list.stack)
    `[[site.i area.i [prod.i src] gen] [tak site sub q.i.mele] p.i.mele]
  ::
  ::
  ?~  res  ~
  ::  top melo hit: no merging necessary
  ::
  ?:  =(0 depth.u.res)
    ?~  cycles.gen.out.u.res  !!
    =*  i   i.cycles.gen.out.u.res
    ?:  (~(has in block-melo.gen) entry.i)  ~
    =.  hits.i     (dive hits.i hit.u.res)
    =.  set.i      (dive set.i site)
    =.  latch.i    site
    `out.u.res
  =/  depth  depth.u.res
  =/  gen  gen.out.u.res
  =/  new-cycle  ,.-.cycles.gen
  =/  rest  ,.+.cycles.gen
  |-
  ?:  =(0 depth)
    ?:  (~(has in block-melo.gen) entry.new-cycle)  ~
    =.  hits.new-cycle     (dive hits.new-cycle hit.u.res)
    =.  set.new-cycle      (dive set.new-cycle site)
    =.  latch.new-cycle    site
    =.  cycles.gen  [new-cycle rest]
    `out.u.res(gen gen)
  ?~  rest  !!
  =.  entry.new-cycle    (min entry.new-cycle entry.i.rest)
  =.  frond.new-cycle    [%deep frond.new-cycle frond.i.rest]
  =.  set.new-cycle      [%deep set.new-cycle set.i.rest]
  =.  process.new-cycle  [%deep process.new-cycle process.i.rest]
  =.  melo.new-cycle     ((~(uno by melo.new-cycle) melo.i.rest) weld-meal)
  =.  hits.new-cycle     [%deep hits.new-cycle hits.i.rest]
  $(rest t.rest, depth (dec depth))
::  given kid and parent subject socks and parent evalsite label, check if
::  the kid sock is compatible with parent for a loop call. heuristic.
::  returns code usage cape if compatible
::
++  close
  |=  [kid-sub=sock par-sub=sock par-site=@uxsite gen=short]
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
++  hint
  |=  [tag=@ hint=sock-anno result=sock-anno gen=short]
  ^-  short
  ?+    tag  gen
      %fast
    ?.  =(& cape.sock.hint)  ~&(>>> %fast-lost-clue gen)
    =*  clue  data.sock.hint
    ?.  ?=([name=$@(@tas [@tas @]) dad=* *] clue)
      ~&(>>> fast-bad-clue+clue gen)
    =/  label=cord
      ?@  name.clue  name.clue
      (rap 3 -.name.clue (scot %ud +.name.clue) ~)
    ::
    ?~  parent=(fast-parent dad.clue)  ~&(>>> fast-bad-clue+clue gen)
    ?~  u.parent
      ::  register root
      ::
      ?.  =(& cape.sock.result)  ~&(>>> %fast-lost-root gen)
      %=  gen
        core.jets  (~(put ju core.jets.gen) ~[label] sock.result)
        root.jets  (~(put ju root.jets.gen) data.sock.result ~[label])
      ==
    ::  register child core
    ::
    =/  axis=@  u.u.parent
    ?.  =(3 (cap axis))  ~&(>>> fast-weird-axis+axis gen)
    =/  batt  (~(pull so sock.result) 2)
    ?.  =(& cape.batt)   ~&(>>> fast-lost-batt+label gen)
    ?.  ?=(^ data.batt)  ~&(>>> fast-atom-batt+data.batt gen)
    =/  fore  (~(pull so sock.result) axis)
    =/  past=(set path)
      %-  %~  uni  in
          ::  root registrations
          ::
          ?.  =(& cape.fore)  ~
          (~(get ju root.jets.gen) data.fore)
      ::  child registrations
      ::
      =/  batt-fore  (~(pull so fore) 2)
      ?.  &(=(& cape.batt-fore) ?=(^ data.batt-fore))  ~
      (~(get ju batt.jets.gen) data.batt-fore)
    ::
    =/  past-list  ~(tap in past)
    |-  ^-  short
    =*  past-loop  $
    ?~  past-list  gen
    =/  pax=path  [label i.past-list]
    =/  socks  ~(tap in (~(get ju core.jets.gen) i.past-list))
    |-  ^-  short
    =*  sock-loop  $
    ?~  socks  past-loop(past-list t.past-list)
    ?.  (~(huge so i.socks) fore)  sock-loop(socks t.socks)
    =/  just-fol=sock  [[& |] data.batt ~]
    =/  template=sock  (~(darn so just-fol) axis i.socks)
    ::
    %=  gen
      core.jets  (~(put ju core.jets.gen) pax template)
      batt.jets  (~(put ju batt.jets.gen) data.batt pax)
    ==
  ==
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
::
++  rewrite-memo
  |=  memoized=(map @uxsite @uxmemo)
  |=  n=nomm
  ^-  nomm
  ~+
  ?^  -.n  [$(n -.n) $(n +.n)]
  ?-    -.n
      %2
    :^  %2  $(n p.n)  $(n q.n)
    ?.  ?=([%site *] site.n)               site.n
    ?~  m=(~(get by memoized) q.p.site.n)  site.n
    memo+u.m
  ::
    ?(%0 %1)      n
    ?(%3 %4)      n(p $(n p.n))
    %s11          n(q $(n q.n))
    ?(%5 %7 %12)  n(p $(n p.n), q $(n q.n))
    ?(%10 %d11)   n(q.p $(n q.p.n), q $(n q.n))
    %6            n(p $(n p.n), q $(n q.n), r $(n r.n))
  ==
::  Analyze s/f pair, then run Nomm interpreter on the result
::  Indirect calls reanalyze
::  Direct calls are verified with subject sock nest checking
::
++  run-nomm
  |=  [s=* f=*]
  ^-  (unit)
  !.
  =/  gen
    ~>  %bout
    (scan &+s f)
  ::
  =/  map-locals=(map @uxsite [less=sock fol=* =nomm])  (malt locals.gen)
  =/  edit  (rewrite-memo (malt memo-loop-entry.gen))
  =.  map-locals
    %-  ~(run by map-locals)
    |=  [sock * =nomm]
    +<(nomm (edit nomm))
  ::
  =.  idxs.memo.gen
    %-  ~(run by idxs.memo.gen)
    |=  meme
    +<(code (edit code))
  ::
  =.  sits.memo.gen
    %-  ~(run by sits.memo.gen)
    |=  meme
    +<(code (edit code))
  ::
  =.  fols.memo.gen
    %-  ~(run by fols.memo.gen)
    |=  l=(list meme)
    %+  turn  l
    |=  meme
    +<(code (edit code))
  ::
  =/  n=nomm
    ?^  m=(~(get by sits.memo.gen) 0v0 0x0)
      code.u.m
    =/  loc  (~(got by map-locals) 0x0)
    ?>  =(f fol.loc)
    nomm.loc
  ::
  =|  trace=(list spot)
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
    ?:  =(0 p.n)
      ~&  '[%0 0]'
      ~&  trace
      ~
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
    ?~  site.n
      ~&  %indirect
      :: !!
      (mole |.(.*(u.s1 u.f1)))
    =;  new=nomm
      ?^  res=(jet u.s1 u.f1)  u.res
      $(s u.s1, n new)
    ?-    -.site.n
        %memo
      =/  m  ~|  p.site.n  (~(got by idxs.memo.gen) p.site.n)
      ?>  =(u.f1 fol.m)
      code.m
    ::
        %site
      =/  loc  ~|  q.p.site.n  (~(got by map-locals) q.p.site.n)
      ?>  =(u.f1 fol.loc)
      nomm.loc
    ==
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
    =?  trace  =(p.p.n %spot)
      =/  pot=(unit spot)  ((soft spot) +.q.p.n)
      ?~  pot  trace
      [u.pot trace]
    ::
    =/  h  $(n q.p.n)
    ?~  h  ~
    $(n q.n)
  ::
      [%12 *]
    ~|  %no-scry  !!
  ==
::  unit of work: subject, formula, if comes from jetted core dissasembly:
::    cons frame? jet registration coordinate
::
+$  todo  [sub=sock fol=* break=(unit [cons=? point=bell])]
::  analysis engine
::
++  ka
  |_  lon=long
  +*  this  .
  ::  Analyze subject/formula pair, descending into jetted cores
  ::
  ++  rout
    |=  [s=* f=*]
    ^+  this
    =/  queu=(list todo)  [[& s] f ~]~
    =|  load=(list todo)
    |-  ^+  this
    =*  cold-loop  $
    ?~  queu
      ?~  load
        :: ~&  ~(wyt by core.jets.lon)
        this
      ~&  >>  cold-loop+(lent load)
      cold-loop(queu (flop load), load ~)
    ?:  ?&(?=(^ break.i.queu) cons.u.break.i.queu)
      ::  merge analysis of an autocons head and tail
      ::
      =*  p  point.u.break.i.queu
      =*  b  back.cole.jets.lon
      =/  heds=(list [sub=sock fol=*])  ~(tap in (~(get ju b) p.p (peg q.p 2)))
      =/  lets=(list [sub=sock fol=*])  ~(tap in (~(get ju b) p.p (peg q.p 3)))
      ~&  >  [%commence-join (lent heds) (lent lets)]
      ?@  fol.i.queu  !!
      |-  ^+  this
      =*  hed-loop  $
      ?~  heds
        ~&  >  %done-joining
        cold-loop(queu t.queu)
      ?.  =(fol.i.heds -.fol.i.queu)
        ~&  >>  %join-head-wrong-fol
        hed-loop(heds t.heds)
      ?.  (~(huge so sub.i.heds) sub.i.queu)
        ~&  >>  %join-head-wrong-sub
        hed-loop(heds t.heds)
      =/  tels  lets
      |-  ^+  this
      =*  tel-loop  $
      ?~  tels  hed-loop(heds t.heds)
      ?.  =(fol.i.tels +.fol.i.queu)
        ~&  >>  %join-tail-wrong-fol
        tel-loop(tels t.tels)
      ?.  (~(huge so sub.i.tels) sub.i.queu)
        ~&  >>  %join-tail-wrong-sub
        tel-loop(tels t.tels)
      ~&  >  joined+p
      =/  join  (~(pack so sub.i.heds) sub.i.tels)
      =.  call.cole.jets.lon  (~(put by call.cole.jets.lon) [join fol.i.queu] p)
      =.  back.cole.jets.lon  (~(put ju back.cole.jets.lon) p join fol.i.queu)
      tel-loop(tels t.tels)
    ::  analyze a formula from a queue, push new tasks in the back queu
    ::
    ::  prepare state
    ::
    =^  here-arm  arm-gen.lon  [arm-gen.lon +(arm-gen.lon)]
    =/  can  scan
    =.  -.gen.can  lon
    =.  here-arm.gen.can  here-arm
    ::  analyze
    ::
    ~?  >  ?=(^ break.i.queu)  [%enter here-arm point.u.break.i.queu]
    ~?  >  ?=(~ break.i.queu)  [%enter here-arm]
    =/  gen=short  (can [sub fol]:i.queu)
    ~&  >  [%done here-arm]
    ::  propagate updates
    ::
    =/  new  ((dif-ju core.jets.gen) core.jets.lon)
    =.  lon  -.gen
    =/  edit  (rewrite-memo (malt memo-loop-entry.gen))
    ::  XX iterate only over the new? might have to keep track of old and new
    ::  memo in short
    ::
    =.  idxs.memo.lon
      %-  ~(run by idxs.memo.lon)
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =.  sits.memo.lon
      %-  ~(run by sits.memo.lon)
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =.  fols.memo.lon
      %-  ~(run by fols.memo.lon)
      |=  l=(list meme)
      %+  turn  l
      |=  m=meme
      ?.  =(here-arm arm.m)  m
      m(code (edit code.m))
    ::
    =?  areas.arms.lon  ?=(^ area.gen)
      (~(put by areas.arms.lon) here-arm u.area.gen)
    ::
    =^  sub-0x0=sock  doors.arms.lon
      ?^  memo-entry.gen
        =/  m  (~(got by idxs.memo.lon) u.memo-entry.gen)
        :-  less-code.m
        (~(put by doors.arms.lon) here-arm [less-code fol code]:m)
      ?^  m=(~(get by sits.memo.lon) here-arm 0x0)
        :-  less-code.u.m
        (~(put by doors.arms.lon) here-arm [less-code fol code]:u.m)
      ?~  locals.gen  !!
      ?>  =(0x0 site.i.locals.gen)
      :-  less.i.locals.gen
      (~(put by doors.arms.lon) here-arm +.i.locals.gen)
    ::
    =/  new-sites=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
      ?~  locals.gen  ~
      %+  roll
        ?.  =(0x0 site.i.locals.gen)  locals.gen
        t.locals.gen
      |=  $:  [site=@uxsite less=sock fol=* =nomm]
              acc=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
          ==
      ^+  acc
      (~(put by acc) [here-arm site] less fol (edit nomm))
    ::
    =.  sites.arms.lon  (~(uni by sites.arms.lon) new-sites)
    %=    cold-loop
        queu  t.queu
    ::
        cole.jets.lon
      ?~  break.i.queu  cole.jets.lon
      =*  p  point.u.break.i.queu
      =/  boot=(pair sock *)  [sub-0x0 fol.i.queu]
      %=  cole.jets.lon
        call  (~(put by call.cole.jets.lon) boot p)
        back  (~(put ju back.cole.jets.lon) p boot)
      ==
    ::
        load
      ::  we sort the list of new jet registrations by ascending order of path
      ::  length, to analyze short paths before the long ones. roll here and 
      ::  flop above cancel each other out
      ::
      %+  roll
        %+  sort
          %+  turn  ~(tap by new)
          |=([p=path q=(set sock)] [(lent p) p q])
        |=([l=[len=@ *] r=[len=@ *]] (lth len.l len.r))
      |:  [[len=*@ p=*path q=*(set sock)] load=load]
      ~&  >  [%enqueu p]
      %-  ~(rep in q)
      |:  [s=*sock load=load]
      =/  batt  (~(pull so s) 2)
      ?.  =(& cape.batt)  ~&(>>> [%cold-miss-batt p] load)
      =*  f  data.batt
      =/  ax=@  2
      |-  ^+  load
      ?.  ?=([^ *] f)  [[s f `[| p ax]] load]
      =.  load  $(f -.f, ax (peg ax 2))
      =.  load  $(f +.f, ax (peg ax 3))
      [[s f `[& p ax]] load]
    ==
  --
::
++  dif-ju
  |*  a=(jug)
  |*  b=_a
  ^+  a
  =/  c=_a  (~(dif by a) b)
  =/  i=_a  (~(int by a) b)
  ?:  =(~ i)  c
  %-  ~(rep by i)
  |=  [[p=_?>(?=(^ i) p.n.i) q=_?>(?=(^ i) q.n.i)] =_c]
  =/  r=_q  (~(get ju b) p)
  =/  s=_q  (~(dif in q) r)
  ?:  =(~ s)  c
  (~(put by c) p s)
::
++  skim-by
  |*  a=(map)
  |*  s=(set _?~(a !! p.n.a))
  |-  ^+  a
  ?~  a  ~
  %.  $(a r.a)
  %~  uni  in
  %.  $(a l.a)
  %~  uni  in
  ?.  (~(has in s) p.n.a)  ~
  [n.a ~ ~]
--
