(ns ricci.tensor
  (:require [clojure.core.match :refer [match]]
            [ricci.derivative]
            [clojure.test :as test]))

(defmacro define
  "Scheme-style curried define"
  [name & values]
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

(defn ensure-map
  "Convert array-like containers to maps from index -> value"
  [mp]
  (if (vector? mp)
    (into {} (map-indexed vector mp))
    mp))

(defn keys
  "A version of keys that can work on vectors"
  [mp]
  (clojure.core/keys (ensure-map mp)))
(defn vals
  "A version of vals that can work on vectors"
  [mp]
  (clojure.core/vals (ensure-map mp)))

(defn map-keys
  "Map a function across a dictionary's keys.

  (map-keys inc {0 'a, 1 'b}) => {1 'a, 2 'b}"
  [f mp]
  (into {}
        (map (fn [[k v]] [(f k) v])
             (ensure-map mp))))
(test/is (= (map-keys inc {0 'a, 1 'b, 2 'c})
            '{1 a, 2 b, 3 c}))

(declare slice)
;;; TODO: change this to TBox? TensorNonField? NonTensor?
;;; These may not transform like tensors, but
;;; they are multilinear maps on something somewhere
(deftype Tensor [dimension type unsliced-getter]
  clojure.lang.IFn
  (#?(:clj invoke :cljs -invoke)
    [this doublet]
    (slice this doublet)))
(defn dimension [tensor] (.-dimension tensor))
(defn tensor? [tensor] (instance? Tensor tensor))
(defn tensor-type [tensor]
  (if (tensor? tensor) (.-type tensor)
      [0 0]))
(defn scalar? [s]
  (= (tensor-type s) [0 0]))


(defn doublet-type [doublet] (mapv count doublet))
(test/is (= [0 0] (doublet-type [{} {}])))
(test/is (= [3 0] (doublet-type [{0 1, 1 1, 2 1} {}])))
(defn full-doublet-for? [tensor doublet]
  (= (tensor-type tensor) (doublet-type doublet)))

(defn unsliced-get [tensor doublet]
  (let [doublet (mapv ensure-map doublet)]
   (assert (full-doublet-for? tensor doublet))
   (or ((.-unsliced-getter tensor) doublet)
       0)))

(defn missing-from-multi [len multi]
  (clojure.set/difference (into #{} (range len))
                          (into #{} (keys multi))))
(test/is (= (missing-from-multi 5 {0 0, 3 3})
           #{1 2 4}))

(defn slice-multi-shift [len multi]
  (let [missing (missing-from-multi len multi)]
    (into [] (sort missing))))
(test/is (= (slice-multi-shift 5 {0 0 3 3})
           [1 2 4]))

(defn slice-merge-multi [len multi new-multi]
  (let [shift (slice-multi-shift len multi)]
    (merge (map-keys shift new-multi)
           multi)))
(test/is (= (slice-merge-multi 5 {0 0} {0 'a 1 'b})
            '{1 a, 2 b, 0 0}))

(defn slice-merge-doublet [type old new]
  (mapv slice-merge-multi type old new))

(defn ensure-doublet [doublet] (mapv ensure-map doublet))
(defn slice [tensor doublet]
  (let [doublet (ensure-doublet doublet)]
    (if (full-doublet-for?  tensor doublet)
      (unsliced-get tensor doublet)
      (Tensor.
       (dimension tensor)
       (mapv - (tensor-type tensor) (doublet-type doublet))
       (fn [new-doublet]
         (slice-merge-doublet (tensor-type tensor) doublet new-doublet))))))

(define ((face N) x)
  "The N-th face map for the standard ordered simplex"
  (if (< x N) x
      (inc x)))
(test/is (= (map (face 0) '(0 1 2 3)) '(1 2 3 4)))
(test/is (= (map (face 2) '(0 1 2 3)) '(0 1 3 4)))
(test/is (= (map (face 3) '(0 1 2 3)) '(0 1 2 4)))
(test/is (= (map (face 4) '(0 1 2 3)) '(0 1 2 3)))

(defn index-insert-at [index axis value]
  (into {axis value}
        (map-keys (face axis) index)))

(defn do-Σ [dim term]
  (apply + (map term (range dim))))
(defmacro Σ [dim dummies & body]
  (match [dummies]
         [[]] 0
         [[n & rest]] `(do-Σ ~dim (fn [~n] (Σ ~dim ~rest ~@body)))))

(defn contract1 [tensor up-axis down-axis]
  (Tensor.
   (dimension tensor)
   (mapv dec (tensor-type tensor))
   (fn [[up down]]
     (Σ (dimension tensor) [n]
        (unsliced-get tensor
                      [(index-insert-at up   up-axis   n)
                       (index-insert-at down down-axis n)])))))

(defn ⊗ [A B]
  {:pre [(= (dimension A) (dimension B))]}
  (let [[uplen dnlen] (tensor-type A)]
    (Tensor.
     (dimension A)
     (mapv + (tensor-type A) (tensor-type B))
     (fn [[Up Dn]]
       (let [[UpA UpB-] (split-with (fn [[key _]] (< key uplen)) Up)
             [DnA DnB-] (split-with (fn [[key _]] (< key dnlen)) Dn)
             UpB (map-keys #(- % uplen) UpB-)
             DnB (map-keys #(- % dnlen) DnB-)]
         (* (unsliced-get A [UpA DnA])
            (unsliced-get B [UpB DnB])))))))

(define ((∂ n) sexp)
  (ricci.derivative/simplify `(~'dd ~sexp [:x ~n])))

(defn euclidean-metric [dim]
  (Tensor.
   dim
   [0 2]
   (fn [[{} {i 0, j 1}]]
     (if (= i j) 1 0))))

((euclidean-metric 3) [[] [0 0]])
((euclidean-metric 3) [[] [1 1]])


(def polar
  (Tensor.
   2
   [0 2]
   (map-keys ensure-doublet
             {[[] [0 0]] 1
              [[] [1 1]] [:x 0]})))


(polar [[] [0 0]])
(polar [[] [1 1]])

(def round
  (Tensor.
   2
   [0 2]
   (map-keys ensure-doublet
             {[[] [0 0]] 1
              [[] [1 1]] '(pow (sin [:x 0]) 2)})))

((∂ 0) (round [[] [1 1]]))

(def upper-half-plane
  (Tensor.
   2
   [0 2]
   (map-keys ensure-doublet
             {[[] [0 0]] '(pow [:x 0] -2)
              [[] [1 1]] '(pow [:x 0] -2)})))
(def poincare-disk
  (Tensor.
   2
   [0 2]
   (map-keys ensure-doublet
             {[[] [0 0]] '(/ (+ (pow [:x 0] 2) (pow [:x 1] 2)))
              [[] [1 1]] '(/ (+ (pow [:x 0] 2) (pow [:x 1] 2)))})))

((∂ 0) (upper-half-plane [[] [0 0]]))
((∂ 1) (upper-half-plane [[] [0 0]]))
((∂ 0) (upper-half-plane [[] [1 1]]))

((∂ 0) (poincare-disk [[] [0 0]]))
((∂ 1) (poincare-disk [[] [0 0]]))


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
   (dimension g)
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
