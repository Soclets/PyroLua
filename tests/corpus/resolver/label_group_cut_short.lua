-- The labels after a label are read before its checks; one cut short stops luac first.
do goto l; local a; ::l:: ;; ::m: end
