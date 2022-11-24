(ns ricci.core)


(def g-sphere-spherical '[[1 0]
                          [0 (pow (sin (X 0)) 2)]])
(def g-flat-polar '[[1 0]
                    [0 (pow r 2)]])
