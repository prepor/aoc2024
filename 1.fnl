(local io (require :io))

(local fun (require :fun))
; (local input (io.lines "1/example.txt"))
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

(table.sort left)
(table.sort right)

(var sum 0)

(each [_ l r (fun.zip left right)]
  (set sum (+ sum (math.abs (- l r)))))

sum




