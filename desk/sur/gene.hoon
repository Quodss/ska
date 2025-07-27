/-  *noir
|%
::  no registerization for now
::
::  Simple stack-based VM that serves as a compilation target for Nomm.
::  Every program pops its subject from the stack and pushes the result
::
::  Global compilation state
::
+$  line
  $:  progs=(map glob-atom prog)
  ==
::
+$  prog  (list op)
::  stack VM ops
::  when compiling %2 to %call and %calf q.nomm should be ignored
::  (never crashes, know the result)
::
::  transfer/consume subject? idiosyncratic applicability
::
+$  op  [o=op-raw eat=?]
+$  op-raw  ::  XX scrying, hints
  $@  $?  %slow  ::  [fol sub ...]  -->  [pro ...]
          %swap  ::  [som mos ...]  -->  [mos som ...]
          %cons  ::  [tel hed ...]  -->  [pro ...]
          %depf  ::  [som ...]      -->  [lob ...], nock 3
          %rise  ::  [som ...]      -->  [som + 1 ...], nock 4
          %equi  ::  [som mos ...]  -->  [lob ...], nock 5
      ==
  $%  [%call p=glob-atom]         ::  [sub ...]      -->  [pro ...], direct call
      [%calf p=glob-atom q=bell]  ::  [sub ...]      -->  [pro ...], direct call, jetted
      [%cnst p=*]                 ::  [sub ...]      -->  [p ...]
      [%skip p=@]                 ::  skip {p} instructions unconditionally
      [%skim p=@]                 ::  [lob ...]      -->  [...], skip {p} instructions if p == 0
      [%edit p=@]                 ::  [don rec ...]  -->  [pro ...], edit {rec} with {don} at {p}
  ==