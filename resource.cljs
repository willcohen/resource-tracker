(ns resource
  (:require [clojure.string :as string]))

(defonce ^:dynamic *resource-context* (atom (list)))

(defonce ^:dynamic *bound-resource-context?* false)

(def ^:dynamic *resource-debug-double-free* nil)

(defn stack-do-release [item]
  (when item
    (try
      (cond
        (instance? cljs.core/Ifn item) (item)
        :else (throw
               (js/Error. "item is not an IFn:" (type item))))
      (catch :default e
        (js/console.warn (string/join [e "Failed to release" item]))))))

(defn stack-track
  ([item dispose-fn]
   (let [log-fn js/console.log]
    (when (and *resource-debug-double-free*
              (some #(identical? item %) @*resource-context*))
     (throw (ex-info "Duplicate track detected; this will result in a double free"
                     {:item item})))
    (when-not *bound-resource-context?*
     (log-fn "Stack resource tracking used but no resource context bound.
This is probably a memory leak.")))
   (swap! *resource-context* conj [item dispose-fn])
   item)
  ([item]
   (stack-track item item)))

(defn stack-ignore-resources
  "Ignore these resources for which pred returns true and do not track them.
  They will not be released unless added again with track"
  [pred]
  (loop [resources @*resource-context*]
    (let [retval (filter (comp pred first) resources)
          leftover (->> (remove (comp pred first) resources)
                        doall)]
      (if-not (compare-and-set! *resource-context* resources leftover)
        (recur @*resource-context*)
        retval))))


(defn stack-ignore
  "Ignore specifically this resource."
  [item]
  (stack-ignore-resources #(= item %))
  item)


(defn stack-release
  "Release this resource and remove it from tracking.  Exceptions propagate to callers."
  [item]
  (when item
    (let [release-list (first (stack-ignore-resources #(= item %)))]
      (when release-list
        (stack-do-release (ffirst release-list))))))


(defn stack-release-resource-seq
  "Release a resource context returned from return-resource-context."
  [res-ctx & {:keys [pred]
              :or {pred identity}}]
  (->> res-ctx
       (filter (comp pred first))
       ;;Avoid holding onto head.
       (map (fn [[_ dispose-fn]]
              (try
                (stack-do-release dispose-fn)
                nil
                (catch :default e e))))
       doall))


(defn stack-release-current-resources
  "Release all resources matching either a predicate or all resources currently tracked.
  Returns any exceptions that happened during release but continues to attempt to
  release anything else in the resource list."
  ([pred]
   (let [leftover (stack-ignore-resources pred)]
     (stack-release-resource-seq leftover)))
  ([]
   (stack-release-current-resources (constantly true))))


(defmacro stack-with-resource-context
  "Begin a new resource context.  Any resources added while this context is open will be
  released when the context ends."
  [& body]
  `(with-bindings {#'*resource-context* (atom (list))
                   #'*bound-resource-context?* true}
     (try
       ~@body
       (finally
         (stack-release-current-resources)))))


(defmacro stack-with-bound-resource-seq
  "Run code and return both the return value and the (updated,appended) resources
  created.
  Returns:
  {:return-value retval
  :resource-seq resources}"
  [resource-seq & body]
  ;;It is important the resources sequences is a list.
  `(with-bindings {#'*resource-context* (atom (seq ~resource-seq))
                   #'*bound-resource-context?* true}
     (try
       (let [retval# (do ~@body)]
         {:return-value retval#
          :resource-seq @*resource-context*})
       (catch :default e#
         (stack-release-current-resources)
         (throw e#)))))


(defmacro return-resource-seq
  "Run code and return both the return value and the resources the code created.
  Returns:
  {:return-value retval
  :resource-seq resources}"
  [& body]
  `(stack-with-bound-resource-seq (list) ~@body))


(def gc-finalization-registry (js/FinalizationRegistry. stack-do-release))
(def gc-weak-reference-set (js/WeakSet.))

(defn- gc-create-reference
  [item dispose-fn ptr-constructor]
  (let [retval (ptr-constructor item gc-finalization-registry
                                (fn [this-ref]
                                  (.delete gc-weak-reference-set this-ref)
                                  (dispose-fn)))]
    (.add gc-weak-reference-set retval)
    retval))

(defn gc-reference
  [item dispose-fn]
  (gc-create-reference item dispose-fn #(into [] '(%1 %2 %3))))

(defn gc-track-gc-only
  [item dispose-fn]
  (gc-reference item dispose-fn)
  item)

(defn gc-track
  [item dispose-fn]
  (-> (gc-reference item dispose-fn)
      (stack-track))
  item)

(defn track-impl
  [item dispose-fn track-type]
  (case track-type
        ; Need to correctly handle sets, so that this double
        ; situation can be handled correctly.
        ;#{"gc" "stack"} (gc-track item dispose-fn)
        "gc" (gc-track-gc-only item dispose-fn)
        "stack" (stack-track item dispose-fn)))

(defn in-stack-resource-context?
  "Returns true if the current running code is inside a stack
  resource context."
  []
  *bound-resource-context?*)

(defn ^:no-doc normalize-track-type
  [track-type]
  (let [track-type (or track-type "auto")]
    (cond
      (= track-type "auto")
      (if (in-stack-resource-context?)
        "stack"
        "gc")
      (string? track-type)
      track-type
      :else
      track-type)))


(defn track
  "Track a resource. If the item is a clojurescript function it can be cleaned up
  by the stack system with no further dispose function. Objects tracked by the
  gc need to have a dispose fn that does *not* reference the tracked object.

  Using stack-based resource tracking when there is no stack resource context
  open will generate a warning every time as it guarantees a memory leak.



  Options:

  * `:track-type` - Track types can be :gc, :stack, [:gc :stack] or :auto with :auto being the default
     tracking type.

     * `gc` - Cleanup will be called just after the original object is garbage collected.
     * `stack` - Get cleaned up when the stack resource context is cleaned up.  This means a stack
        returns context must be open.
     * `auto`: Will use stack if a stack is open and gc if one is not."
  ([item keymap]
   (let [track-type (.-tracktype keymap)
         dispose-fn (.-disposefn keymap)
         track-type (normalize-track-type track-type)]
     (when (and (= track-type "gc")
                (not dispose-fn))
       (throw (ex-info "gc track types must have a dispose function that does *not*
reference item."
                       {:item item
                        :track-type track-type})))
     (let [dispose-fn (or dispose-fn item)]
       (when-not (fn? dispose-fn)
         (throw (ex-info
                   "The dispose method must be a clojurescript function."
                         {:dispose-fn dispose-fn})))
       (track-impl item dispose-fn track-type))))
  ([item]
   (track item nil)))


(defmacro stack-resource-context
  "Stack resource context.  When this context unwinds, stack resource declared within
  will be released."
  [& body]
  `(stack-with-resource-context ~@body))


(defmacro releasing!
  "Resources allocated within this stack frame will be released when
  this code returns. Synonym for [[stack-resource-context]]."
  [& body]
  `(stack-with-resource-context ~@body))


(defn chain-resources
  "Chain an older resource to a newer (derived) one such that the older
  resource cannot go out of gc scope before the newer resource has.  This
  allows you to create 'sub' objects and ensure the parent object cannot get
  cleaned up before 'sub' objects.


  This is a very costly way of doing this and if misused it can lead to false
  OOM situations.  The reason is that the link to the parent object is only broken
  *after* the GC run so it takes as many gc runs as the depth of the object graph so
  your code can easily create object graphs faster than it will cause gc runs.

  Because of this it is much better to just have a member variable or metadata
  that points back to the parent."
  [new-resource old-resource]
  (gc-track-gc-only new-resource (constantly old-resource)))
