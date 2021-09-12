# Multi-Splay Trees

Contents:

1. **Splay Trees**
2. **Dynamic Optimality**
3. **Tango Trees**
4. **Multi-Splay Trees**
5. **Theorems**

References:

1. *Dynamic Optimality and Multi-Splay Trees, Sleator & Wang [SW04]*
2. *Dynamic Optimality– Almost; Demaine, Harmon, Iacono & Patrascu [DHIP04]*
3. *Properties of Multi-Splay Trees; Derryberry, Sleator & Wang [DSW]*
4. *Self-adjusting binary search trees; Sleator & Tarjan [ST85]*
5. *Lower bounds for accessing binary search trees with rotations; Robert Wilber [Wil89]*
6. *[CMSS00]*
7. *[Tar85]*
8. *A note on some tree similarity measures; K. Culik II and D. Wood [CW82]*
9. *Rotation distance, triangulations and hyperbolic geometry; Sleator, Tarjan and Thurston. [STT85]*



## Introduction:

Dynamic Optimality was conjectured for Splay Trees in [ST85]. Since then, the largest bit of progress in this sub-field was the introduction of Tango trees, a BST-algorithm that is $O(\log\log n)$-competitive  [DHIP04] and has many desirable properties. However, there are several access patterns  [WHICH?] for which they are worse than other BST algorithms by a factor of $O(\log \log n)$.

Multi-Splay Trees are an attempt to deal with this problem. They may be viewed as a variant of splay trees.

Nice things:

* MSTs are $O(\log \log n)$-competitive.
* MSTs have an amortized bound of $O(\log n)$, for access to a BST.


## Basic Notions

* **Competitive Ratio;** An algorithm $A$ has a competitive ratio of $\alpha$, if for all sequences $X$ of operations, we have that:

  $$COST_A(X)\leq \alpha COST_{OPT}(X)$$ 

  where $COST_A(X)$ is the cost of algorithm $A$ on the sequence $X$, and $COST_{OPT}(X)$ is the cost of the best algorithm for the same sequence. 

* **Access Sequence**; A sequence of succesful searches (*accesses*) to a BST data structure, for a static universe of keys ${1,2,\cdots,n}.$  An access sequence $X$ is given by a sequence of keys, $x_1,x_2,\cdots,x_m$.

* **BST Access Algorithm**; An algorithm for serving an access $x_i$, using unit cost operations on a single pointer. At the start of the search, the pointer is initialised to the root of the BST. The permitted operations for this pointer are:

  1. Move to left-child.
  2. Move to right-child.
  3. Move to parent.
  4. Rotate pointer and node.

  We say that a BST algorithm <u>*touches*</u> a node, if the pointer move to, or is initialised to that node.

  In general, the time taken by a BST to execute an access sequence of keys $x_1, x_2, \cdots, x_m$, is considered to be the number of unit-cost operations used, which is the same as the number of nodes touched by the access algorithm. The access-algorithm may be specified to <u>always start at the root</u> or <u>begin from the last access location</u>.

  The fundamental question of algorithmic complexity for BST-algorithms is simple: which among these algorithms is asymptotically-optimal? Unfortunately, we don’t know the answer - not even in the simplest case where the set of keys saved are static and no insertions or deletions are allowed. But guesses have been made.

* **Online BST-structure;** A BST where each node is *augmented* with a constant amount (conventionally $O(\log n)$) of extra information and each unit-cost operation may alter this extra information. For each access, the choice of next operation to be performed is determined completely by the data and augmented information of the node currently pointed to. I.e., the algorithm’s behaviour depends only on the past.  Notice that any online BST-structure which needs only $O(1)$ augmented words per node, will have running time dominated by the order of the number of operations required to  maintain the structure.  Ideally then, the augmentations are as small as possible - Red-Black trees require only 1 extra bit, while Splay trees require none at all.
  In contrast, an offline algorithm may be able to pick operations dependent also on *future* operations.

* **Optimality;** Given any access-sequence $X$, there is a BST-structure that executes it optimally. Let $OPT(T,X)$ be the number of unit-cost operations made by this fastest BST-structure for $X$ on a BST $T$. Then $OPT(T,X)$ is the fastest that any *offline* algorithm can manage the access-sequence, $X$. We say that an online BST-structure is *dynamically optimal* if it executes all access-sequences $X$, in $O(OPT(T,X))$. More generally, we say that an online BST-structure is $c$-*competitive* if it executes all *sufficiently long* access-sequences in time, at most $c\cdot OPT(T,X)$ .

==Goal: We are looking for an online BST-structure that is $O(1)$-competitive using only $O(1)$ augmented bits per node.==

*Note.* Culik and Wood [CW82] proved that any binary tree with $n$ nodes can be converted into a tree with any other configuration of the same nodes, using at most $2n-2$ rotations. This means that if a tree’s initial configuration $T$ differs from the best-possible initial state $T^\prime$ , then $OPT(T,X)$ differs from $OPT(T^\prime,X)$ by at most $2n-2$. Then, so long as $m=\Omega(n)$, we can ignore the initial tree entirely in what follows. In fact, Sleator, Tarjan and Thurston [STT86] were able to further reduce this bound so that only $2n-6 (n\geq 10)$ rotations are in fact, necessary.

---



## Splay Trees

This is an online BST-structure where instead of strict balancing schemes like that found in AVL, or weaker schemes like RB, every BST-op is followed by *splaying*. This is a sequence of operations that take the last element acted upon, and make the requisite rotations to turn it into the root of the BST. There are three situations:

1. <u>Zig</u>; Required node is the child of the root. Only one left or right rotation is needed.
2. <u>Zig-Zig</u>; The required node is the left-child of a left-child, or symmetrically, the right-child of a right-child. Two rotations in the same direction are required, first on the parent, then on the node itself.
3. <u>Zig-Zag</u>; The rquired node is the left-child of a right-child, or the right-child of a left-child. Here we use two rotations in opposite directions.

In [ST85], it was shown that the amortized cost of splaying a node is bounded by $O(\log n)$ for a tree of $n$ nodes. To get to this result, they began by assuming that each node $x$ in the BST has an arbitrary, but fixed weight $w(x)$. The *size* $s(x)$ of each node $x$, is the sum over all weights of nodes in the subtree rooted at $x$, and, the *rank* of the node $x$, is given by $r(x)=\log s(x)$. The potential of the tree is then defined to be the sum of the ranks of all its nodes. In the following expression, the running-time of the splaying operations was approximated by counting the number of rotations required. If no rotations were used, unit cost was assumed.

* **Lemma.** (Access Lemma) [ST85] The amortized time to splay a tree with root $t$, at a node $x$, is given by $3(r(t)-r(x))+1 = O(\log \left( \frac{s(t)}{s(x)} \right))$.

Several bounds have been proved for Splay Trees including the working-set bound [ST85], the static-finger bound [ST85], the sequential access bound [Tar85], and the dynamic finger bound [CMSS00], showing that Splay trees are $O(m\log n)$ for certain kinds of access-sequences, but these actually only take $\Theta(m)$ time to execute on splay trees in the offline mode. In fact, there are no known BSTs that are better than $O(\log n)$-competitive with the best offline structure.

* **Conjecture**. (Dynamic Optimality) [ST85] Splay-trees are $O(1)$-competitive; i.e., Splay trees are $O(OPT(X))$ for *any* access-sequence $X$.

---



## Tango Trees

We lack knowledge of how the optimal BST-algorithm works, so we can instead conjecture about the the lower-bounds for competitive ratios with BST-algorithms. Our strategy will be to find a lower-bound $IL(X)$, such that, $\forall X: OPT(X)\geq IL(X)$, and then show that $TANGO(X)\geq O(\log \log n)\cdot IL(X)$. 	

Let us begin with an access sequence $X=\{x_1,x_2,\cdots,x_m\}$ as usual. Let $P$ be the complete, static BST on the set of keys $\{x_1,\cdots,x_n\}$. Augment each node with 1-bit of data, labeled $$MR$$  (“most recent”) , so that $MR(x_i)=1$, *if and only if*, the most recent access routed through $x_i$ went to its right sub-tree, and $MR(x_i)=0$, otherwise. Since $P$ is a complete BST, each access can only result in $O(\log n)$ bit-flips for the augmentation. Then, we define:

* **Interleave Lower Bound;**  $IL(X) =$ Total number of changes in MR bits during accesses for $X$. 

In fact, Wilber [Wil89] showed that:

$$OPT(X) \geq IL(X)/2 - O(n) + m$$

Or more concisely, $OPT(X)=\Omega(IL(X))$. 

Define,

* **Preferred Path;** The *preferred path* in a BST augmented with MR bits, is found by traversing from the root to a leaf by going left when $MR(x_i)=0$ and going right when $MR(x_i)=1$. 

By removing the edges that constitute the preferred path in $P$, we obtain a disjoint union of $O(\log n)$ subtrees. Define,

* **Preferred Path (PPD) Decomposition;** 
  $$PPD(T) = \{PP(T)\} \cup PPD\{T-PP(T)\}$$

  where the latter application of $PPD$ applies to each of the subtrees in $\{T-PP(T)\}$.

Note that PPDs can change multiple times depending on the access sequence.



---



## Multi-Splay Trees

For simplicity, assume that there are precisely $n=2^{k}-1(k \in \mathbb{N})$ nodes. Let $P$ be the perfectly-balanced BST made from these $n$ nodes, called the *reference tree*. By construction, the depth of any node in $P$ is at most $\log(n+1)$. Analogous to the ideas used to implement the Tango algorithm above, each node in $P$ will have a *preferred child*, with a chain of such nodes referred to as a *preferred path*. This partitions the set of all keys in the BST into $2^{k-1}$ subsets which each correspond to a preferred-path.

The Multi-Splay Tree (MST) data-structure is a BST, say $T$, over the set of keys $x_i(i=1,\cdots,n)$ that evolves over time, whose composition can be described relative to the reference-tree in the following sense:

* Every edge in an MST is either *solid* or *dashed*.

* A set of vertices connected via solid edges, is called a *splay tree*. <u>There is a bijection between the set of splay trees in an MST and the set of preferred paths in the reference tree.</u> In particular, the set of nodes in a splay tree is identical to the nodes the compose the corresponding preferred path.

  * The *splay subtree* of a node $x$ refers to all the nodes in the same splay tree as $x$, that have $x$ as an ancestor (including $x$).
  * *Note.* This also means that $P$ can be 

* In addition to the usual left, right and parent pointers, each node $x$ of $T$ is also augmented with the following data, relative to $P$:

  * *Pdepth*: Depth of the node in $P$. The root has depth $1$. In any splay tree, no two nodes have the same Pdepth.
  * *Pheight*: Height of the node in $P$. Leaves have height $0$.
  * *mindepth*: The minimum Pdepth for nodes in the splay-subtree rooted at $x$.
  * *treesize*: The number of nodes in the splay subtree rooted at $x$.
  * *isroot*: Boolean variable that indicates if the edge from this node to its parent is dashed. 

* To maintain the correspondence between $P$ and $T$, we make use of *switch* operations in $P$, that simply switch the preferred child of a given node.

  * If a node $x$ is accessed, traverse the path from $x$ back up to the root, using a *switch* operation at every non-preferred child node, so that the root-to-$x$ path is now a preferred path.

  * *Note.* The number of switches that occur in $P$ due to a single access is equal to the increase in the interleave bound due to that access. 

  * **Algorithm.** Each switch in $P$ can be simulated in $T$ by, at most, three splay operations and two changes in *is_root* bits. 
    *Implementation.* Let $y$ be the node whose preferred child we want to switch, in $P$. To begin with, consider both children to be preferred. Now, consider the set $S$ consisting of all nodes in the subtree of $P$ containing $y$ and using <u>only</u> preferred edges. This set admits a natural partition into four subsets, $L, R, U$ and $\{y\}$, where; $L$ represents nodes in the left subtree of $y$ in $P$; $R$ represents nodes in the right subtree of $y$ in $P$; and, $U$ represents those nodes above $y$ in $P$. Sorting $S$ by key,  we get continuous regions $L$ and $R$, that are separated by $\{y\}$.

    In $T$, the splay tree containing $y$ can be decomposed as $L\cup U \cup \{y\}$. After the switch in $P$, it becomes $R\cup U \cup \{y\}$. So the required sequence of MST operations must remove $L$ and replace it with $R$.

    First, define a method *RightMost* that takes a node $x$ and integer $depth$ as input, and returns the node with greatest key-value and $Pdepth$ less than $depth$, in the splay subtree of $x$.

    *RightMost(x, depth)*:

    1. If the input, $x$ is $NULL$, OR, $x.isroot$ is true, OR, $x.mindepth=depth$, return $NULL$.
    2. Set $right=RightMost(x.right,depth)$.
    3. If $right\neq NULL$, return $right$.
    4. If $x.Pdepth<depth$, return $x$.
    5. Return $RightMost(x.left, depth)$.

    Analogously, define *LeftMost(x, depth)*. We also require two additional methods that carry out the splaying. Call the first $Splay(x)$, which splays $x$ to the root as usual. Let the second method be called $Splay2(x,y)$, so that $x$ is splayed up to the level of its ancestor $y$. I.e., $y$ is then the child of $x$. Finally, we can now describe a procedure to switch a node’s preferred child from left to right.

    *Left2Right(y, upper):* 
    
    1) $Splay(y)$, so that it becomes a root.
    2) Find $y$‘s predecessor $z$ in $U$.
       1) 
    3) *(Remove $L$ from the splay tree of $y$)*
       1) Splay $z$ within its splay subtree, so that it becomes the left child of $y$. 
       2) The right child of $z$ is the least common ancestor for $L$ in $T$. Set $z.right$ as root.  
    4) *(Merge $R$ into the splay tree of $y$)*
       1) Traverse from $y$ to its successor $x$ in $U$, and splay this node within its splay subtree, so that it becomes the right child of $y$.  
       2) Similar to Step 4, the left child of $x$ is now the least common ancestor of $R$ in $T$. Set $x.left$ as root. 
    
    Notice that this process only uses splay ops in $U\cup\{y\}$. Thus when an access is executed in $T$, the subsequent calls to this method to reflect the switched in $P$ still respect the $O(\log n)$ amortized bound for access in a BST.
    
  * sa

