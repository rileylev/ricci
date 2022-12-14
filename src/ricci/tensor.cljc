(ns ricci.tensor
  (:require [clojure.core.match :refer [match]]))

(defmacro define [name & values]
  (let [topname (first (flatten (list name)))
        docstr  (and (> (count values) 1)
                     (string? (first values))
                     (first values))]
    (loop [level  0
           name   name
           values values]
      (match name
        ([fname & args] :seq)
        (recur (inc level)
               fname
               `((fn ~(gensym (str topname "-level" level "-"))
                   [~@args]
                   ~@values))),
        _ `(def ~name ~@(if docstr [docstr]) ~@values)))))

;; "smart index" tensor design
;; multi-index
;; I := (i₀,i₁,i₂,... iₖ₋₁) ==> (def I {0 i₀, 1 i₁, 2 i₂, ... (dec k) iₖ₋₁})
;; Most tensor manipulations are then built up by manipulating multi-indices
;;
;; doublet: up multi index, down multi index
;; [I J]
;;
;; tensor : doublet -> component
;;
;; Aᴵ_J => (A [I J])
;; Aⁱ⁰ ⁱ¹ ⁱ²ⱼ₀ ⱼ₁ ⱼ₂ => (A [{0 i0, 1 i1, 2 i2} {0 j0, 1 j1, 2 j2}]})
;;
;; symbolic ricci calculus ≈
;; tensor algebra over field of elementary functions with N indeterminates

(defn ensure-map [mp]
  (if (vector? mp)
    (into {} (map-indexed vector mp))
    mp))
(defn keys [mp]
  (clojure.core/keys (ensure-map mp)))
(defn vals [mp]
  (clojure.core/vals (ensure-map mp)))

(defn map-keys [f mp]
  (into {}
        (map (fn [[k v]] [(f k) v])
             (ensure-map mp))))
(assert (= (map-keys inc {0 'a, 1 'b, 2 'c})
           '{1 a, 2 b, 3 c}))

(defn map-vals [f mp]
  (into {}
        (map (fn [[k v]] [k (f v)])
             (ensure-map mp))))
(assert (= (map-vals inc {'a 0, 'b 1, 'c 2})
           '{a 1, b 2, c 3}))

(declare slice)
(deftype Tensor [dimension type unsliced-getter]
  clojure.lang.IFn
  (#?(:clj invoke :cljs -invoke)
    [this doublet]
    (slice this doublet)))

(defn doublet-type [doublet] (mapv count doublet))
(assert (= [0 0] (doublet-type [{} {}])))
(assert (= [3 0] (doublet-type [{0 1, 1 1, 2 1} {}])))
(defn full-doublet-for? [tensor doublet]
  (= (.-type tensor) (doublet-type doublet)))

(defn unsliced-get [tensor doublet]
  (let [doublet (mapv ensure-map doublet)]
   (assert (full-doublet-for? tensor doublet))
   (or ((.-unsliced-getter tensor) doublet)
       0)))

(defn missing-from-multi [len multi]
  (clojure.set/difference (into #{} (range len))
                          (into #{} (keys multi))))
(assert (= (missing-from-multi 5 {0 0, 3 3})
           #{1 2 4}))

(defn slice-multi-shift [len multi]
  (let [missing (missing-from-multi len multi)]
    (into [] (sort missing))))
(assert (= (slice-multi-shift 5 {0 0 3 3})
           [1 2 4]))

(defn slice-merge-multi [len multi new-multi]
  (let [shift (slice-multi-shift len multi)]
    (merge (map-keys shift new-multi)
           multi)))
(assert (= (slice-multi 5 {0 0} {0 'a 1 'b})
           '{1 a, 2 b, 0 0}))

(defn slice-merge-doublet [type old new]
  (mapv slice-merge-multi type old new))

(defn slice [tensor [up  down  :as doublet]]
  (if (full-doublet-for?  tensor doublet)
    (unsliced-get tensor doublet)
    (Tensor.
     (.-dimension tensor)
     (mapv - (.-type tensor) (doublet-type doublet))
     (fn [new-doublet]
       (slice-merge-doublet (.-type tensor) doublet new-doublet)))))

(define ((face N) x)
  "The N-th face map for the standard ordered simplex"
  (if (< x N) x
      (inc x)))
(defn index-insert-at [index axis value]
  (into {axis value}
        (map-keys (face axis) index)))
(defn contract1 [tensor up-axis down-axis]
  (Tensor.
   (.-dimension tensor)
   (mapv dec (.-type tensor))
   (fn [[up down]]
     (apply +
            (map
             #(unsliced-get tensor
                            [(index-insert-at up   up-axis   %)
                             (index-insert-at down down-axis %)])
             (range (.-dimension tensor)))))))

(defn ⊗ [A B]
  (assert (= (.-dimension A) (.-dimension B)))
  (let [[uplen dnlen] (.-type A)]
    (Tensor.
     (.-dimension A)
     (mapv + (.-type A) (.-type B))
     (fn [[Up Dn]]
       (let [[UpA UpB] (split-with (fn [[key _]] (< key uplen)) Up)
             [DnA DnB] (split-with (fn [[key _]] (< key dnlen)) Dn)]
         (* (unsliced-get A [UpA DnA])
            (unsliced-get B [UpB DnB])))))))

(define ((∂ n) sexp)
  (ricci.derivative/simplify `(~'dd ~sexp [:x ~n])))

(defn euclidean-metric [dim]
  (Tensor.
   dim
   [0 2]
   (fn [[_ {i 0, j 1}]]
     (if (= i j) 1 0))))

((euclidean-metric 3) [{} {0 0, 1 0}])
((euclidean-metric 3) [[] [1 1]])

(def polar
  (Tensor.
   2
   [0 2]
   {[{} {0 0, 1 0}] 1
    [{} {0 1, 1 1}] [:x 0]}))


(polar [{}  {0 0, 1 0} ])
(polar [{}  {0 1, 1 1} ])

(def round
  (Tensor.
   2
   [0 2]
   {[{} {0 0, 1 0}] 1
    [{} {0 1, 1 1}] '(pow (sin [:x 0]) 2)}))

((∂ 0) (round [{} {0 1, 1 1}]))
((∂ 0) (round [[] [1 1]]))

(def upper-half-plane
  (Tensor.
   2
   [0 2]
   {[{} {0 0, 1 0}] '(pow [:x 0] -2)
    [{} {0 1, 1 1}] '(pow [:x 0] -2)}))
(def poincare-disk
  (Tensor.
   2
   [0 2]
   {[{} {0 0, 1 0}] '(/ (+ (pow [:x 0] 2) (pow [:x 1] 2)))
    [{} {0 1, 1 1}] '(/ (+ (pow [:x 0] 2) (pow [:x 1] 2)))}))




((∂ 0) (upper-half-plane [{} {0 0, 1 0}]))
((∂ 1) (upper-half-plane [{} {0 0, 1 0}]))

((∂ 0) (poincare-disk [{} {0 0, 1 0}]))
((∂ 1) (poincare-disk [{} {0 0, 1 0}]))


(defn christoffel-first-kind [g a b c]
  (ricci.derivative/simplify
   `(~'* 1/2
     (~'+
      (~'+
       ~((∂ a) (g [[] [b c]]))
       ~((∂ b) (g [[] [a c]])))
      (~'- ~((∂ c) (g [[] [a b]])))))))
(christoffel-first-kind round 0 1 1)


(defn Γ1st [g]
  (Tensor.
   (.-dimension g)
   [0 3]
   (fn [[{} I]]
     (christoffel-first-kind g (I 0) (I 1) (I 2)))))

(round [[] [1 1]])

((Γ1st round) [[] [0 1 1]])

(defn t+ [A B]
  {:pre [(= (dimension A) (dimension B))
         (= (tensor-type A) (tensor-type B))]}
  (Tensor.
   (dimension A)
   (tensor-type A)
   (fn [doublet]
     (+ (A doublet) (B doublet)))))
(defn t- [A]
  (Tensor.
   (dimension A)
   (tensor-type A)
   (fn [doublet]
     (- (A doublet)))))

(defn scale [scalar tensor]
  {:pre [(scalar? scalar)
         (tensor? tensor)]}
  (Tensor.
   (dimension tensor)
   (tensor-type tensor)
   (fn [doublet]
     (* scalar (tensor doublet)))))
