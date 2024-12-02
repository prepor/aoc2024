(local fun (require :fun))
(local fennel (require :fennel))
(local input (io.lines "2/input.txt"))

(fn split-by-spaces [str]
  (icollect [s (string.gmatch str "[^%s]+")] s))

(fn strs->numbers [strs]
  (-> (fun.map tonumber strs) fun.totable))

(fn is-safe [level]
  (let [is-increasing (< 0 (- (. level 1) (. level 2)))]
    (fun.all 
      (fn [l1 l2]
        (let [diff (- l1 l2)]
          (and (= is-increasing (< 0 diff))
               (< 0 (math.abs diff) 4))))
      (fun.zip level (fun.drop 1 level)))))

(fn variants [level]
  (->>
  (fun.chain [level]
             (fun.map
               (fn [i] (fun.chain (fun.take (- i 1) level) (fun.drop i level)))
               (fun.enumerate level)))
  (fun.map fun.totable)))

(var safe 0)

(each [l input]
  (let [level (-> l (split-by-spaces) (strs->numbers))]
    (if (fun.any is-safe (variants level))
      (set safe (+ safe 1)))))

safe
