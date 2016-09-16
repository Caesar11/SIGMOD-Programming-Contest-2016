# SIGMOD-Programming-Contest-2016

This repository is about the source code of team **gStreamPKU**,
which is one of five finalists of [SIGMOD Programming Contest 2016](http://dsg.uwaterloo.ca/sigmod16contest/).
We present our solution on ACM SIGMOD/PODS conference on June 30th, 2016 in San Franciso, USA.
You can get more details about our solution from [our poster](http://dsg.uwaterloo.ca/sigmod16contest/downloads/gStreamPKU_poster.pdf). 

## Team Member:
+ Shuo Han
+ Jiaze Chen
+ Lei Zou(Advisor)

## Task Description
The task is to solve the shortest path problem on a dynamic graph with
directed but unweighted edges. Firstly the test harness sends the initial
graph. The time spent on loading, pre-processing or indexing the initial
graph will not count into the total execution time.

Then the workload comes in batches. Each batch consists of three types of
operations:

+ (1) A u v -- add an edge from vertex u to v.
+ (2) D u v -- delete the edge from u to v, if it exists.
+ (3) Q u v -- query the distance of the shortest path from u to v.

Our goal is to answer these queries correctly, and as quickly as possible.

## Solution Overview

### Bidirectional BFS
To reduce the overall search space, we search from both forward direction and backward direction. At each iteration, we select the direction which has smaller sum of degrees of vertices needed to explore, and expand this direction to its next level. As long as two directions meet at one vertex, the shortest distance is the number of explored levels of both directions.

### Fully Concurrent Query Execution within a Batch
When processing a batch, we maintain a Delta Graph over all the A/D operations. The Delta Graph preserves not only updated edges in this batch, but also each edge's A/D time stamp list. For example, if the edge e(u,v) is deleted at time t1, then is added back at time t6, then its time stamp list is [(t1,D), (t6,A)].
Furthermore, if an edge already exists in the version of graph before this batch, we add (t0,A) to the head of its time stamp list. Otherwise, we add (t0,D). If e(u,v) already exists before this batch, finally its time stamp list is [(t0,A), (t1,D), (t6,A)].

For each Q operation, its time stamp is also recorded. Before query execution, we need to remove all the edges who involves in at least one D operation in this batch from data graph, then all the rest edges in data graph can be explored "safely" within this batch's queries. For a query with time stamp tq, an edge e(u,v) from Delta Graph should be explored if and only if: we find the element with the largest time stamp who is smaller than tq in e(u,v)'s time stamp list, and this element's operation label is 'A'. Considering the example above, if a query's time stamp is t3, then e(u,v) can not be explored. But for another query whose time stamp is t7, e(u,v) is valid.

Through data graph combining with Delta Graph we built, all the queries in this batch can be executed concurrently.

### Bit Compression of Graph's Edge Lists
Instead of store the data graph in adjacent lists directly, we compress the adjacent list into bitset style. Each element in compressed adjacent list consists of offset field and state field. For example, if vertex 1 has forward neighbors 2, 3, 4, 6, 64, 70, its original adjacent list is [1: 2->3->4->6->64->70]. After compressed, it becomes [1: (0, '01011100')->(8, '01000001')]. In order to facilitate, we only shows 8-bit integer compression in this example. In practice, we use 64-bit integer for a better performance.

The BFS procedure is also modified to fit in the edge list's compress style. Vertices needed to be explored are also store in the bitset compress style.

Through the bit compression technique, vertices with large degrees can be explored more efficiently, because we can process its neighbors once a batch when they are compressed into one 64-bit integer. Therefore, this technique improves performance significantly for social network graphs.

### Improving Cache's Hit Rate
To improve cache's hit rate, we rearrange data graph's storage in memory. Neighbor vertices in each vertex's adjacent edge list are arranged continuously in physical address. Improvement on memory locality reduces the number of cache miss.

Graphs with lower graph bandwidth have a better locality. To reduce the data graph's bandwidth, we use the Reverse Cuthill-McKee Algorithm to reassign vertices id.

We also warm up cache by executing a batch of random generated queries before outputting 'R'.

## Dependencies
+ Jemalloc 3.6.0
+ Intel Threading Building Blocks 4.3


