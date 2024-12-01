
(local io (require :io))
(local cljlib (require :io.gitlab.andreyorst.cljlib))

(local fun (require :fun))
; (local input (io.lines "1/example2.txt"))
(local input (io.lines "1/input.txt"))

(fn split-by-spaces [str]
  (icollect [s (string.gmatch str "[^%s]+")] s))

(fn strs->numbers [strs]
  (-> (fun.map tonumber strs) fun.totable))

(local [left right] [[] []])

(each [line input]
  (let [[l r] (-> (split-by-spaces line) (strs->numbers))]
    (table.insert left l)
    (table.insert right r)))

(local freq (cljlib.frequencies right))

(var sum 0)

(each [_ l (ipairs left)]
  ; (print "---" l (. freq l))
  (set sum (+ sum (* l (or (. freq l) 0)))))

sum

