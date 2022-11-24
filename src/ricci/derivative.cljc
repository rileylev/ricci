(ns ricci.derivative)

(def alg-rules
  '[((+ ?x 0 )      ?x),
    ((+ 0  ?x)      ?x),
    ((* ?x 1 )      ?x)
    ((* 1  ?x)      ?x)
    ((* ?x 0 )      0)
    ((* 0  ?x)      0)

    ((pow ?x 0)    1),
    ((pow ?x 1)    ?x)

    ((- 0)         0)
    ((/ 1)         1)
    ((* (/ ?x) ?x) 1)
    ((* ?x (/ ?x)) 1)])

(def deriv-rules
  '[((dd c?k ?v) 0),
    ((dd ?x ?x)  1),
    ((dd (:x c?a) (:x c?b)) 0)

    ((dd (+ ?u ?v) ?x) (+ (dd ?u ?x) (dd ?v ?x))),
    ((dd (* ?u ?v) ?x) (+ (* (dd ?u ?x) ?v        )
                          (* ?u         (dd ?v ?x)))),

    ((dd (/ ?u) ?x) (dd (pow ?u -1) ?x))

    ((dd (pow ?u c?n) ?x) (* (* ?n (pow ?u (+ ?n -1)))
                             (dd ?u ?x)))
    ((dd (exp ?u) ?x) (* (exp ?u) (dd ?u ?x)))
    ((dd (ln ?u) ?x) (* (/ ?u) (dd ?u ?x)))
    ((dd (sin ?u) ?x) (* (cos ?u) (dd ?u ?x)))
    ((dd (cos ?u) ?x) (- (* (sin ?u) (dd ?u ?x))))])

(def constant? number?)

(defn parse-pattern-var
  "If input is a symbol of the form of a pattern variable, parse it,
   into [kind name]. Otherwise, evaluate to false.

  Pattern variables are symbols. They start with
     ? when kind= :plain    (can match anything),
    c? when kind= :constant (it can only match a constant)."
  [var]
  (and (symbol? var)
       (let [[prefix name] (.split (str var) "\\?" 2) ]
         (case prefix
           ""  [:plain    name]
           "c" [:constant name]
           false))))

(defonce ^{:doc "The value to denote match failure."}
  fail (gensym "fail"))

(defn merge-unique
  "Merges bindings together. If bindings conflict, give up return `fail`.
  If any inputs are `fail`, give up and return fail.

  binding = fail | {name value, ...}"
  [& dicts]
  (if (some #{fail} dicts)
    fail
    (let [fail-if-not= #(if (= %1 %2) %1 fail)
          merged (apply merge-with fail-if-not= dicts)]
      (if (some #{fail} (vals merged))
        fail
        merged))))

(defn same-count? [col1 col2]
  (= (count col1) (count col2)))

(defn match
  "Takes a pattern and an expression. If they match,
  return a dicitonary(map) of bindings. Otherwise, return fail."
  [pattern expression]
  (if (seqable? pattern)
    (if (and (seqable? expression)
             (same-count? pattern expression))
      (apply merge-unique (map match pattern expression))
      fail)
    (if-let [[kind name] (parse-pattern-var pattern)]
      (case kind
        :plain    {name expression}
        :constant (if-not (constant? expression) fail
                          {name expression}))
      (if (= pattern expression) {} fail))))

(defn surely-get [dict key]
  (let [pair (find dict key)]
    (assert pair)
    (val pair)))

(defn instantiate [skeleton dict]
  {:pre [(not= dict fail)]}
  (if (seqable? skeleton)
    (map #(instantiate % dict) skeleton)
    (if-let [[_ name] (parse-pattern-var skeleton)]
      (surely-get dict name)
      skeleton)))

(defn find1 [pred? col] (first (filter pred? col)))

(defn simplify1 [rules expression]
  (let [dict-skeletons (for [[pattern skeleton] rules]
                         [(match pattern expression) skeleton])
        success?       (fn [[dict _]] (not= dict fail))]
    (if-let [[dict skeleton] (find1 success? dict-skeletons)]
      (instantiate skeleton dict)
      expression)))

(def arithmetic-dict {'+ + '- - '* * '/ /})
(defn arithmetic-simplify [expr]
  (or
   (if (seqable? expr)
     (let [[sym-op & args] expr]
       (if-let [op (arithmetic-dict sym-op)]
         (let [args (map arithmetic-simplify args)]
           (if (every? constant? args)
             (apply op args))))))
   expr))

(defn simplify-deep1 [rules expression]
  (let [expression (arithmetic-simplify expression)]
   (if (seqable? expression)
     (simplify1 rules
                (map #(simplify-deep1 rules %)
                     expression))
     expression)))

(defn zip [& cols] (apply map vector cols))
(defn adjacents [col] (zip col (rest col)))
(defn adjacent-filter [bipred? col]
  (filter (fn [[x y]] (bipred? x y))
          (adjacents col)))
(defn adjacent-find1-pair [bipred? col]
  (first (adjacent-filter bipred? col)))

(defn fix [f init]
  (first (adjacent-find1-pair = (iterate f init))))

(def ^:dynamic *default-rules* (concat alg-rules deriv-rules))
(defn simplify
  ([expression] (simplify *default-rules* expression))
  ([rules expression]
   (fix #(simplify-deep1 rules %) expression)))

(simplify1 deriv-rules (simplify deriv-rules '(dd (* x (pow x 2)) x)))

(simplify (concat alg-rules deriv-rules) '(dd (pow (sin x) 2) x))
