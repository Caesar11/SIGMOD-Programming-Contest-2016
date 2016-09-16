#include "iostream"
#include "cstdio"
#include "cstring"
#include "map"
#include "set"
#include "queue"
#include "cstdint"
#include "unordered_set"
#include "unordered_map"
#include "cassert"
#include "algorithm"
#include "ctime"
#include "tbb/concurrent_queue.h"
#include "tbb/atomic.h"
#include "tbb/task_scheduler_init.h"
#include "tbb/parallel_for.h"
#include "mmintrin.h"
#include "sys/time.h"
using namespace std;
using namespace tbb;
#define ALWAYS_INLINE inline __attribute__((always_inline))

bool is_bit_comp_open = false; // whether use edge bit compression strategy.

const int MAXEDGECOUNT = 20000000;
const int MAXNODECOUNT = 10000000;
const int OPLISTLENGTH = 200000;
const int THREADNUM = 24;

int node_cnt = 0;
int edge_cnt = 0, redge_cnt = 0;
unordered_map<uint32_t, int> node_id;
unordered_map<uint64_t, int> edge_id, redge_id;

struct EdgePool
{
    int to;
    int prev, next;
};
EdgePool edges[MAXEDGECOUNT], redges[MAXEDGECOUNT];
int first[MAXNODECOUNT] __attribute__((aligned(16))), last[MAXNODECOUNT] __attribute__((aligned(16)));
int rfirst[MAXNODECOUNT] __attribute__((aligned(16))), rlast[MAXNODECOUNT] __attribute__((aligned(16)));
int in_deg[MAXNODECOUNT], out_deg[MAXNODECOUNT];

int visit_label_count = 0;

int GetNodeId(uint32_t orgid)
{
    auto p = node_id.find(orgid);
    if (p != node_id.end())
        return p->second;
    return node_id[orgid] = node_cnt++;
}

void GraphInit()
{
    edge_cnt = redge_cnt = 0;
    edge_id.clear(); redge_id.clear();
    memset(first, -1, sizeof(int) * MAXNODECOUNT);
    memset(last, -1, sizeof(int) * MAXNODECOUNT);
    memset(rfirst, -1, sizeof(int) * MAXNODECOUNT);
    memset(rlast, -1, sizeof(int) * MAXNODECOUNT);
    memset(in_deg, 0, sizeof(int) * MAXNODECOUNT);
    memset(out_deg, 0, sizeof(int) * MAXNODECOUNT);
}

void AddOriginalEdge(int idx, int idy) {
    uint64_t idxy = (((uint64_t)idx << 32) | idy);
    if (edge_id.find(idxy) != edge_id.end()) return;
    edge_id[idxy] = edge_cnt;
    edges[edge_cnt].to = idy; 
    if (first[idx] == -1) {
        first[idx] = edge_cnt;
        last[idx] = edge_cnt;
        edges[edge_cnt].prev = -1;
        edges[edge_cnt].next = -1;
    }else{
        edges[last[idx]].next = edge_cnt;
        edges[edge_cnt].prev = last[idx];
        edges[edge_cnt].next = -1;
        last[idx] = edge_cnt;
    }
    edge_cnt++;
    out_deg[idx]++;
}
void AddReverseEdge(int idx, int idy) {
    uint64_t idxy = (((uint64_t)idx << 32) | idy);
    if (redge_id.find(idxy) != redge_id.end()) return;
    redge_id[idxy] = redge_cnt;
    redges[redge_cnt].to = idx;
    if (rfirst[idy] == -1) {
        rfirst[idy] = redge_cnt;
        rlast[idy] = redge_cnt;
        redges[redge_cnt].prev = -1;
        redges[redge_cnt].next = -1;
    }else {
        redges[rlast[idy]].next = redge_cnt;
        redges[redge_cnt].prev = rlast[idy];
        redges[redge_cnt].next = -1;
        rlast[idy] = redge_cnt;
    }
    redge_cnt++;
    in_deg[idy]++;
}
void AddNewEdge(int idx, int idy) {
    uint64_t idxy = (((uint64_t)idx << 32) | idy);
    if (edge_id.find(idxy) != edge_id.end()) return;
    edge_id[idxy] = edge_cnt;
    edges[edge_cnt].to = idy; 
    if (first[idx] == -1) {
        first[idx] = edge_cnt;
        last[idx] = edge_cnt;
        edges[edge_cnt].prev = -1;
        edges[edge_cnt].next = -1;
    }else{
        edges[last[idx]].next = edge_cnt;
        edges[edge_cnt].prev = last[idx];
        edges[edge_cnt].next = -1;
        last[idx] = edge_cnt;
    }
    edge_cnt++;
    redge_id[idxy] = redge_cnt;
    redges[redge_cnt].to = idx;
    if (rfirst[idy] == -1) {
        rfirst[idy] = redge_cnt;
        rlast[idy] = redge_cnt;
        redges[redge_cnt].prev = -1;
        redges[redge_cnt].next = -1;
    }else {
        redges[rlast[idy]].next = redge_cnt;
        redges[redge_cnt].prev = rlast[idy];
        redges[redge_cnt].next = -1;
        rlast[idy] = redge_cnt;
    }
    redge_cnt++;
    out_deg[idx]++; in_deg[idy]++;
}

void DeleteEdge(int idx, int idy) {
    uint64_t idxy = (((uint64_t)idx << 32) | idy);
    if (edge_id.find(idxy) == edge_id.end()) return;
    int eid = edge_id[idxy];
    if (edges[eid].prev == -1) {
        if (edges[eid].next == -1){
            last[idx] = first[idx] = -1;
        }else{
            edges[edges[eid].next].prev = -1;
            first[idx] = edges[eid].next;
        }
    }else {
        edges[edges[eid].prev].next = edges[eid].next;
        if (edges[eid].next == -1){
            last[idx] = edges[eid].prev;
        }else{
            edges[edges[eid].next].prev = edges[eid].prev;
        }
    }
    eid = redge_id[idxy];
    if (redges[eid].prev == -1) {
        if (redges[eid].next == -1) {
            rlast[idy] = rfirst[idy] = -1;
        }else {
            redges[redges[eid].next].prev = -1;
            rfirst[idy] = redges[eid].next;
        }
    }else {
        redges[redges[eid].prev].next = redges[eid].next;
        if (redges[eid].next == -1) {
            rlast[idy] = redges[eid].prev;
        }else {
            redges[redges[eid].next].prev = redges[eid].prev;
        }
    }
    edge_id.erase(idxy);
    redge_id.erase(idxy);
    out_deg[idx]--; in_deg[idy]--;
}

struct Edge
{
    int u, v;
};

bool edge_cmp(const pair<int, int>& a, const pair<int, int>& b)
{
    if (a.first == b.first) return a.second < b.second;
    return a.first < b.first;
}
bool redge_cmp(const pair<int, int>& a, const pair<int, int>& b)
{
    if(a.second == b.second) return a.first < b.first;        
    return a.second < b.second;
}

// assume that time stamp within a batch will not exceed uint16_t's range.
struct OpTimeStamp
{
    uint16_t time, op; // op=0 for add; op=1 for delete; op=2 for time vec end. 
};
struct Operation
{
    Edge e;
    OpTimeStamp ts;
};
bool operation_cmp(const Operation& a, const Operation& b)
{
    if (a.e.u == b.e.u) return a.e.v < b.e.v;
    return a.e.u < b.e.u;
}

ALWAYS_INLINE int fastscan(uint32_t &x)
{
    char c;
    x = 0;
    c=getchar_unlocked();

    while (c == ' ' || c == '\n' || c =='\t') c=getchar_unlocked();
    if (c == 'S') return 0;
    for(;(c>47 && c<58);c=getchar_unlocked())
        x = (x<<1) + (x<<3) + c - 48;
    return 1;
}
ALWAYS_INLINE void fastscan(char &c)
{
    c=getchar_unlocked();
    while (c == ' ' || c == '\n'|| c =='\t') c=getchar_unlocked();
}
struct OperationList
{
    int u_cnt, q_cnt;
    Operation update[OPLISTLENGTH], query[OPLISTLENGTH];
    uint16_t tid;

    int readBatchOp()
    {
        char c;
        uint32_t org_u, org_v;
        tid = 0;
        u_cnt = q_cnt = 0;
        for (;;) {
            fastscan(c);
            if (c == 'F') break;
            if (c == EOF) return 0;
            fastscan(org_u);
            fastscan(org_v);
            tid++;
            if (c == 'Q') {
                query[q_cnt].e.u = GetNodeId(org_u);
                query[q_cnt].e.v = GetNodeId(org_v);
                query[q_cnt].ts.time = tid;
                query[q_cnt].ts.op = q_cnt++; // query's op is query idx.
            } else if (c == 'A') {
                update[u_cnt].e.u = GetNodeId(org_u);
                update[u_cnt].e.v = GetNodeId(org_v);
                update[u_cnt].ts.time = tid;
                update[u_cnt++].ts.op = 0;
                
            } else {
                if (node_id.find(org_u) != node_id.end() && 
                    node_id.find(org_v) != node_id.end()) {
                    update[u_cnt].e.u = GetNodeId(org_u);
                    update[u_cnt].e.v = GetNodeId(org_v);
                    update[u_cnt].ts.time = tid;
                    update[u_cnt++].ts.op = 1;            
                }
            }
        }
        return 1;        
    }
};
OperationList op_list;

// typedef int BitState;
// #define CTZ __builtin_ctz
// const int BIT_LEN = 32;

typedef uint_fast64_t BitState;
#define CTZ __builtin_ctzll
const int BIT_LEN = 64;

const int BIT_MASK = BIT_LEN - 1;
const int BIT_POW = CTZ(BIT_LEN);
const int BITBASE = sizeof(BitState) * 8;
const int MAXBITNODECOUNT = 6400000 / BITBASE;

struct alignas(16) BitNode
{
    int base;
    BitState state;

    BitNode(){}
    BitNode(int _b, BitState _s): base(_b), state(_s) {}
};

// const int BITEDGE_POOL_SIZE = 0x04000000;
// const int BITEDGE_PADDING_SIZE = 8;
const int BITEDGE_POOL_SIZE = 0x08000000;
const int BITEDGE_PADDING_SIZE = 16;
const int MIN_PADDING_SIZE = 12;
// const int BITEDGE_PADDING_SIZE = 8;
// const int MIN_PADDING_SIZE = 6;
struct BitEdges
{
    unordered_map<uint64_t, int> edge_pos, redge_pos;
    int start_pos[MAXNODECOUNT] __attribute__((aligned(16))), rstart_pos[MAXNODECOUNT] __attribute__((aligned(16)));
    int edge_num[MAXNODECOUNT] __attribute__((aligned(16))), redge_num[MAXNODECOUNT] __attribute__((aligned(16)));
    int edge_capa[MAXNODECOUNT] __attribute__((aligned(16))), redge_capa[MAXNODECOUNT] __attribute__((aligned(16)));
    int end_pos, rend_pos;
    BitNode *pool, *rpool;

    BitEdges()
    {
        pool = new BitNode[BITEDGE_POOL_SIZE];
        rpool = new BitNode[BITEDGE_POOL_SIZE];
    }
    
    void init(vector<pair<int, int>>& edge_vec)
    {        
        end_pos = rend_pos = 0;
        memset(start_pos, -1, sizeof(int) * MAXNODECOUNT);
        memset(rstart_pos, -1, sizeof(int) * MAXNODECOUNT);
        memset(edge_num, 0, sizeof(int) * MAXNODECOUNT);
        memset(redge_num, 0, sizeof(int) * MAXNODECOUNT);

        sort(edge_vec.begin(), edge_vec.end(), edge_cmp);
        int pre_u = -1;
        for (auto iter=edge_vec.begin();iter!=edge_vec.end();++iter)
        {          
            int &u = iter->first, &v = iter->second;
            int vbase = (v >> BIT_POW);
            BitState vbit = ((BitState)1 << (v & BIT_MASK));
            uint64_t uv = (((uint64_t)u << 32) | vbase);            
            if (u != pre_u)
            {
                if (pre_u != -1)
                {
                    int reserve_size = (BITEDGE_PADDING_SIZE - (edge_num[pre_u] % BITEDGE_PADDING_SIZE)) % BITEDGE_PADDING_SIZE;
                    if (reserve_size < MIN_PADDING_SIZE) reserve_size += BITEDGE_PADDING_SIZE;
                    edge_capa[pre_u] = edge_num[pre_u] + reserve_size;
                    end_pos += reserve_size;
                }
                start_pos[u] = end_pos;
                pre_u = u;
            }
            if (edge_pos.find(uv) != edge_pos.end()) // existed bit edge
            {
                int cur_pos = start_pos[u] + edge_pos[uv];                
                pool[cur_pos].state |= vbit;
            }
            else // new bit edge
            {
                pool[end_pos].base = vbase;
                pool[end_pos].state = vbit;
                edge_pos[uv] = edge_num[u]++;
                end_pos++;             
            }
            
        }
        if (pre_u != -1)
        {
            int reserve_size = (BITEDGE_PADDING_SIZE - (edge_num[pre_u] % BITEDGE_PADDING_SIZE)) % BITEDGE_PADDING_SIZE;
            if (reserve_size < MIN_PADDING_SIZE) reserve_size += BITEDGE_PADDING_SIZE;
            edge_capa[pre_u] = edge_num[pre_u] + reserve_size;
            end_pos += reserve_size;
        }

        sort(edge_vec.begin(), edge_vec.end(), redge_cmp);
        int pre_v = -1;
        for (auto iter=edge_vec.begin();iter!=edge_vec.end();++iter)
        {          
            int &u = iter->first, &v = iter->second;
            int ubase = (u >> BIT_POW);
            BitState ubit = ((BitState)1 << (u & BIT_MASK));
            uint64_t vu = (((uint64_t)v << 32) | ubase);            
            if (v != pre_v)
            {
                if (pre_v != -1)
                {
                    int reserve_size = (BITEDGE_PADDING_SIZE - (redge_num[pre_v] % BITEDGE_PADDING_SIZE)) % BITEDGE_PADDING_SIZE;
                    if (reserve_size < MIN_PADDING_SIZE) reserve_size += BITEDGE_PADDING_SIZE;
                    redge_capa[pre_v] = redge_num[pre_v] + reserve_size;
                    rend_pos += reserve_size;
                }
                rstart_pos[v] = rend_pos;
                pre_v = v;
            }
            if (redge_pos.find(vu) != redge_pos.end()) // existed bit edge
            {
                int cur_pos = rstart_pos[v] + redge_pos[vu];                
                rpool[cur_pos].state |= ubit;
            }
            else // new bit edge
            {
                rpool[rend_pos].base = ubase;
                rpool[rend_pos].state = ubit;
                redge_pos[vu] = redge_num[v]++;
                rend_pos++;       
            }            
        }
        if (pre_v != -1)
        {
            int reserve_size = (BITEDGE_PADDING_SIZE - (redge_num[pre_v] % BITEDGE_PADDING_SIZE)) % BITEDGE_PADDING_SIZE;
            if (reserve_size < MIN_PADDING_SIZE) reserve_size += BITEDGE_PADDING_SIZE;
            redge_capa[pre_v] = redge_num[pre_v] + reserve_size;
            rend_pos += reserve_size;
        }
    }

    void print() // for debug
    {
        for (int i=0;i<node_cnt;++i)
            if (start_pos[i] != -1 && edge_num[i] > 0)
            {
                printf("%d:", i);
                vector<int> tmp_vec;
                for (int j=0;j<edge_num[i];++j)
                {
                    BitState vbit = pool[start_pos[i] + j].state;
                    int vbase = (pool[start_pos[i] + j].base << BIT_POW);
                    while (vbit)
                    {
                        int v = vbase + CTZ(vbit);
                        tmp_vec.push_back(v);
                        vbit &= (vbit - 1);
                    }  
                }                    
                sort(tmp_vec.begin(), tmp_vec.end());
                for (int j=0;j<tmp_vec.size();++j)
                    printf(" %d", tmp_vec[j]);
                printf("\n");
            }
        printf("---------\n");
        for (int i=0;i<node_cnt;++i)
            if (rstart_pos[i] != -1 && redge_num[i] > 0)
            {
                printf("%d:", i);
                vector<int> tmp_vec;
                for (int j=0;j<redge_num[i];++j)
                {
                    int ubit = rpool[rstart_pos[i] + j].state;
                    int ubase = (rpool[rstart_pos[i] + j].base << BIT_POW);
                    while (ubit)
                    {
                        int u = ubase + CTZ(ubit);
                        tmp_vec.push_back(u);
                        ubit &= (ubit - 1);
                    } 
                }  
                sort(tmp_vec.begin(), tmp_vec.end());
                for (int j=0;j<tmp_vec.size();++j)
                    printf(" %d", tmp_vec[j]);
                printf("\n");
            }
    }

    void AddEdge(Edge& e)
    {
        int &u = e.u, &v = e.v;
        int vbase = (v >> BIT_POW);
        BitState vbit = ((BitState)1 << (v & BIT_MASK));
        uint64_t uv = (((uint64_t)u << 32) | vbase);
        int ubase = (u >> BIT_POW);
        BitState ubit = ((BitState)1 << (u & BIT_MASK));
        uint64_t vu = (((uint64_t)v << 32) | ubase);  

        if (edge_pos.find(uv) != edge_pos.end())
        {
            int cur_pos = start_pos[u] + edge_pos[uv];
            pool[cur_pos].state |= vbit;
        }
        else
        {
            if (start_pos[u] == -1)
            {
                start_pos[u] = end_pos;
                edge_capa[u] = BITEDGE_PADDING_SIZE;
                end_pos += BITEDGE_PADDING_SIZE;
            }
            if (edge_num[u] == edge_capa[u])
            {
                memcpy(pool + end_pos, pool + start_pos[u], sizeof(BitNode) * edge_num[u]);
                // cerr << "memcpy pool" << endl;
                start_pos[u] = end_pos;
                edge_capa[u] += BITEDGE_PADDING_SIZE;
                end_pos += edge_capa[u];
            }
            int cur_pos = start_pos[u] + edge_num[u];
            pool[cur_pos].base = vbase;
            pool[cur_pos].state = vbit;
            edge_pos[uv] = edge_num[u]++;
        }

        if (redge_pos.find(vu) != redge_pos.end())
        {
            int cur_pos = rstart_pos[v] + redge_pos[vu];
            rpool[cur_pos].state |= ubit;
        }
        else
        {
            if (rstart_pos[v] == -1)
            {
                rstart_pos[v] = rend_pos;
                redge_capa[v] = BITEDGE_PADDING_SIZE;
                rend_pos += BITEDGE_PADDING_SIZE;
            }
            if (redge_num[v] == redge_capa[v])
            {
                memcpy(rpool + rend_pos, rpool + rstart_pos[v], sizeof(BitNode) * redge_num[v]);
                // cerr << "memcpy rpool" << endl;
                rstart_pos[v] = rend_pos;
                redge_capa[v] += BITEDGE_PADDING_SIZE;
                rend_pos += redge_capa[v];
            }
            int cur_pos = rstart_pos[v] + redge_num[v];
            rpool[cur_pos].base = ubase;
            rpool[cur_pos].state = ubit;
            redge_pos[vu] = redge_num[v]++;       
        }
    }

    void DeleteEdge(Edge& e)
    {
        int &u = e.u, &v = e.v;
        int vbase = (v >> BIT_POW);
        BitState vbit = ((BitState)1 << (v & BIT_MASK));
        uint64_t uv = (((uint64_t)u << 32) | vbase);
        int ubase = (u >> BIT_POW);
        BitState ubit = ((BitState)1 << (u & BIT_MASK));
        uint64_t vu = (((uint64_t)v << 32) | ubase);

        if (edge_pos.find(uv) != edge_pos.end())
        {
            int cur_pos = start_pos[u] + edge_pos[uv];
            pool[cur_pos].state = ((pool[cur_pos].state ^ vbit) & pool[cur_pos].state);
            // but not remove this bit node even when it is deleted to 0.
        }

        if (redge_pos.find(vu) != redge_pos.end())
        {
            int cur_pos = rstart_pos[v] + redge_pos[vu];
            rpool[cur_pos].state = ((rpool[cur_pos].state ^ ubit) & rpool[cur_pos].state);
            // but not remove this bit node even when it is deleted to 0.          
        }
    }

    bool isEdgeExist(Edge& e)
    {
        int &u = e.u, &v = e.v;
        int vbase = (v >> BIT_POW);
        BitState vbit = ((BitState)1 << (v & BIT_MASK));
        uint64_t uv = (((uint64_t)u << 32) | vbase);
        if (edge_pos.find(uv) == edge_pos.end()) return false;
        return ((pool[start_pos[u] + edge_pos[uv]].state & vbit) != 0);   
    }
};
BitEdges bitEdges;

struct DeltaGraphS
{
    int head[MAXNODECOUNT], rhead[MAXNODECOUNT];
    uint16_t batch_h[MAXNODECOUNT], batch_rh[MAXNODECOUNT], batch_cnt;
    int end[OPLISTLENGTH * 4], rend[OPLISTLENGTH * 4];
    int next[OPLISTLENGTH * 4], rnext[OPLISTLENGTH * 4], time_head[OPLISTLENGTH * 4]; 
    OpTimeStamp time_pool[OPLISTLENGTH * 4];
    int delta_edge_cnt, time_cnt;    

    map<uint64_t, int> edge2head;

    OpTimeStamp ts_val[OPLISTLENGTH * 4];
    int ts_next[OPLISTLENGTH * 4], ts_cnt;

    OpTimeStamp ts_A0, ts_D0, ts_END;

    Edge add_edge[OPLISTLENGTH];
    int add_edge_cnt;

    DeltaGraphS()
    {
        memset(batch_h, 0, sizeof(uint16_t) * MAXNODECOUNT);
        memset(batch_rh, 0, sizeof(uint16_t) * MAXNODECOUNT);
        memset(head, -1, sizeof(int) * MAXNODECOUNT);
        memset(rhead, -1, sizeof(int) * MAXNODECOUNT);
        batch_cnt = 0;
        ts_A0.op = 0; ts_A0.time = 0;
        ts_D0.op = 1; ts_D0.time = 0;
        ts_END.op = 2; ts_END.time = 0;
    }

    void build(Operation *u_list, int u_cnt)
    {
        this->clear();

        // collect each edge's time stamp vector.
        for (int i=u_cnt-1;i>=0;--i)
        {
            uint64_t uv = (((uint64_t)u_list[i].e.u << 32) | u_list[i].e.v);    
            ts_val[ts_cnt] = u_list[i].ts;
            ts_next[ts_cnt] = (edge2head.find(uv) == edge2head.end()) ? -1 : edge2head[uv];
            edge2head[uv] = ts_cnt;
            if (ts_val[ts_cnt].op == 0 && ts_next[ts_cnt] == -1)           
                add_edge[add_edge_cnt++] = u_list[i].e;           
            ts_cnt++;
        }

        // construct delta edge's time stamp vector into a static adjacent list.
        for (auto iter=edge2head.begin();iter!=edge2head.end();++iter)
            addEdgeTimeVec(iter->first, iter->second);
    }

    void addEdgeTimeVec(uint64_t uv, int head_pos)
    {
        Edge e; e.u = (uv >> 32); e.v = (uv & 0xffffffffLL);
        int &u = e.u, &v = e.v;

        end[delta_edge_cnt] = v; rend[delta_edge_cnt] = u;
        time_head[delta_edge_cnt] = time_cnt;        
        next[delta_edge_cnt] = (batch_h[u] != batch_cnt) ? -1 : head[u];
        rnext[delta_edge_cnt] = (batch_rh[v] != batch_cnt) ? -1 : rhead[v];
        batch_h[u] = batch_cnt; batch_rh[v] = batch_cnt;
        head[u] = delta_edge_cnt; rhead[v] = delta_edge_cnt;
        delta_edge_cnt++;

        if (is_bit_comp_open)
            time_pool[time_cnt++] = (bitEdges.isEdgeExist(e)) ? ts_A0 : ts_D0;
        else
            time_pool[time_cnt++] = (edge_id.find(uv) != edge_id.end()) ? ts_A0 : ts_D0;
        
        while (head_pos != -1)
        {  
            time_pool[time_cnt++] = ts_val[head_pos];
            head_pos = ts_next[head_pos];
        }
        time_pool[time_cnt++] = ts_END;
    }

    void clear()
    {
        batch_cnt++;
        delta_edge_cnt = 0;
        time_cnt = 0;
        ts_cnt = 0;
        add_edge_cnt = 0;
        edge2head.clear();
    }
};
DeltaGraphS dGraphS;

ALWAYS_INLINE bool LegalV(OpTimeStamp *time_vec, uint16_t qtime)
{
    while (((time_vec+1)->op != 2) &&
           ((time_vec+1)->time < qtime))
        time_vec++;

    return time_vec->op == 0;
}


int *visit[THREADNUM], *rvisit[THREADNUM];
int *visit_mem_pool, *rvisit_mem_pool;
BitState *bit_state[THREADNUM], *rbit_state[THREADNUM];
BitState *bit_state_mem_pool, *rbit_state_mem_pool;
int *points[THREADNUM][2], *rpoints[THREADNUM][2];
int *point_mem_pool, *rpoint_mem_pool;

void AllocBfsMem()
{
    visit_mem_pool = new int[THREADNUM * MAXNODECOUNT];
    rvisit_mem_pool = new int[THREADNUM * MAXNODECOUNT];
    memset(visit_mem_pool, -1, sizeof(int) * THREADNUM * MAXNODECOUNT);
    memset(rvisit_mem_pool, -1, sizeof(int) * THREADNUM * MAXNODECOUNT);
    bit_state_mem_pool = new BitState[THREADNUM * MAXBITNODECOUNT];
    rbit_state_mem_pool = new BitState[THREADNUM * MAXBITNODECOUNT];
    for (int i=0;i<THREADNUM;++i)
    {
        visit[i] = visit_mem_pool + (i * MAXNODECOUNT);
        rvisit[i] = rvisit_mem_pool + (i * MAXNODECOUNT);
        bit_state[i] = bit_state_mem_pool + (i * MAXBITNODECOUNT);
        rbit_state[i] = rbit_state_mem_pool + (i * MAXBITNODECOUNT);
    }

    int dim1_size = MAXNODECOUNT * 2;
    int dim2_size = MAXNODECOUNT;

    point_mem_pool = new int[THREADNUM * dim1_size];
    rpoint_mem_pool = new int[THREADNUM * dim1_size];
    for (int i=0;i<THREADNUM;++i)
        for (int j=0;j<2;++j)
        {
            points[i][j] = point_mem_pool + (i * dim1_size + j * dim2_size);
            rpoints[i][j] = rpoint_mem_pool + (i * dim1_size + j * dim2_size);
        }
}

concurrent_queue<int> idle_pid;
int ans[OPLISTLENGTH], visit_label[OPLISTLENGTH];

// Bidir-BFS, without edge bit compression.
int (*BfsFuncPtr)(Operation&, int,
                    int *, int *,
                    int *[2], int *[2]);

int BidirBFS(Operation& query, int count,
                int *_visit, int *_rvisit,
                int *_points[2], int *_rpoints[2])
{
    if (query.e.u == query.e.v) return 0;
    int level = 0, rlevel = 0;
    int sz[2], rsz[2];  
    memset(sz, 0, sizeof(sz)); memset(rsz, 0, sizeof(rsz));

    _points[0][sz[0]++] = query.e.u;
    _rpoints[0][rsz[0]++] = query.e.v;
    _visit[query.e.u] = count; _rvisit[query.e.v] = count;
    while(sz[level & 1] != 0 && rsz[rlevel & 1] != 0)
    {
        int now = level & 1, next = now ^ 1;
        int rnow = rlevel & 1, rnext = rnow ^ 1;

        if (sz[now] <= rsz[rnow])
        {
            sz[next] = 0;
            for (int i = 0; i < sz[now]; ++i)
            // for (int i = sz[now] - 1; i >= 0; --i)
            {
                int u = _points[now][i];
                for (int j = first[u]; j != -1; j = edges[j].next)
                {
                    int v = edges[j].to;
                    if (_visit[v] != count)
                    {
                        if (_rvisit[v] == count) return level + rlevel + 1;
                        _visit[v] = count;
                        _points[next][sz[next]++] = v;                
                    }
                }
                // traverse adjacent edges in DeltaGraphS.
                if (dGraphS.batch_h[u] == dGraphS.batch_cnt)
                // if (__builtin_expect(dGraphS.batch_h[u] == dGraphS.batch_cnt, 0))
                {
                    for (int pos = dGraphS.head[u];pos!=-1;pos=dGraphS.next[pos])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[pos]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.end[pos];                            
                            if (_visit[v] != count)
                            {
                                if (_rvisit[v] == count) return level + rlevel + 1;
                                _visit[v] = count;
                                _points[next][sz[next]++] = v;
                            }
                        }
                    }
                }
            }
            level ++;
        }else {
            rsz[rnext] = 0;
            for (int i = 0; i < rsz[rnow]; ++i)
            // for (int i = rsz[rnow] - 1; i >= 0; --i)
            {
                int u = _rpoints[rnow][i];
                for (int j = rfirst[u]; j != -1; j = redges[j].next)
                {
                    int v = redges[j].to;
                    if (_rvisit[v] != count)
                    {
                        if (_visit[v] == count) return level + rlevel + 1;
                        _rvisit[v] = count;
                        _rpoints[rnext][rsz[rnext]++] = v;
                    }
                }
                // traverse adjacent redges in DeltaGraphS.
                if (dGraphS.batch_rh[u] == dGraphS.batch_cnt)
                // if (__builtin_expect(dGraphS.batch_rh[u] == dGraphS.batch_cnt, 0))
                {
                    for (int pos=dGraphS.rhead[u];pos!=-1;pos=dGraphS.rnext[pos])
                    { 
                        OpTimeStamp *time_vec = &(dGraphS.time_pool[dGraphS.time_head[pos]]);                       
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.rend[pos];                            
                            if (_rvisit[v] != count)
                            {
                                if (_visit[v] == count) return level + rlevel + 1;
                                _rvisit[v] = count;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                        }
                    }
                }
            }
            rlevel ++;
        }
    }
    return -1;
}

int BidirBFS_Deg(Operation& query, int count,
                    int *_visit, int *_rvisit,
                    int *_points[2], int *_rpoints[2])
{
    if (query.e.u == query.e.v) return 0;

    int level = 0, rlevel = 0;
    int sz[2], rsz[2];  
    memset(sz, 0, sizeof(sz)); memset(rsz, 0, sizeof(rsz));
    int sum_deg = 0, rsum_deg = 0;

    _points[0][sz[0]++] = query.e.u;
    _rpoints[0][rsz[0]++] = query.e.v;
    _visit[query.e.u] = count; _rvisit[query.e.v] = count;
    while(sz[level & 1] != 0 && rsz[rlevel & 1] != 0)
    {
        int now = level & 1, next = now ^ 1;
        int rnow = rlevel & 1, rnext = rnow ^ 1;
        if (sum_deg <= rsum_deg)
        {
            sz[next] = 0;
            for (int i = 0; i < sz[now]; ++i)
            // for (int i = sz[now] - 1; i >= 0; --i)
            {
                int u = _points[now][i];
                for (int j = first[u]; j != -1; j = edges[j].next)
                {
                    int v = edges[j].to;
                    if (_visit[v] != count)
                    {
                        if (_rvisit[v] == count) return level + rlevel + 1;
                        _visit[v] = count;
                        _points[next][sz[next]++] = v;                
                    }
                }
                // traverse adjacent edges in DeltaGraphS.
                if (dGraphS.batch_h[u] == dGraphS.batch_cnt)
                {
                    for (int pos = dGraphS.head[u];pos!=-1;pos=dGraphS.next[pos])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[pos]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.end[pos];                            
                            if (_visit[v] != count)
                            {
                                if (_rvisit[v] == count) return level + rlevel + 1;
                                _visit[v] = count;
                                _points[next][sz[next]++] = v;
                            }
                        }
                    }
                }
            }
            sum_deg = 0;
            for (int i = 0; i < sz[next]; ++i)
            // for (int i = sz[next] - 1; i >= 0; --i)
                sum_deg += out_deg[_points[next][i]];
            level ++;

        }else {
            rsz[rnext] = 0;
            for (int i = 0; i < rsz[rnow]; ++i)
            // for (int i = rsz[rnow] - 1; i >= 0; --i)
            {
                int u = _rpoints[rnow][i];
                for (int j = rfirst[u]; j != -1; j = redges[j].next)
                {
                    int v = redges[j].to;
                    if (_rvisit[v] != count)
                    {
                        if (_visit[v] == count) return level + rlevel + 1;
                        _rvisit[v] = count;
                        _rpoints[rnext][rsz[rnext]++] = v;
                    }
                }
                // traverse adjacent redges in DeltaGraphS.
                if (dGraphS.batch_rh[u] == dGraphS.batch_cnt)
                {
                    for (int pos=dGraphS.rhead[u];pos!=-1;pos=dGraphS.rnext[pos])
                    { 
                        OpTimeStamp *time_vec = &(dGraphS.time_pool[dGraphS.time_head[pos]]);                       
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.rend[pos];                            
                            if (_rvisit[v] != count)
                            {
                                if (_visit[v] == count) return level + rlevel + 1;
                                _rvisit[v] = count;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                        }
                    }
                }
            }
            rsum_deg = 0;
            for (int i = 0; i < rsz[rnext]; ++i)
            // for (int i = rsz[rnext] - 1; i >= 0 ; --i)
                rsum_deg += in_deg[_rpoints[rnext][i]];
            rlevel ++;
        }
    }
    return -1;
}

class ConcurrentQueryProcessor
{
    Operation *queries;

public:
    void operator() (const blocked_range<size_t>& r) const
    {
        for (size_t i=r.begin();i!=r.end();++i)
        {
            int pid;
            while (!idle_pid.try_pop(pid));
            ans[i] = (*BfsFuncPtr)(queries[i], visit_label[i],
                                      visit[pid], rvisit[pid], 
                                      points[pid], rpoints[pid]);           
            idle_pid.push(pid);
        }
    }
    ConcurrentQueryProcessor(Operation *_queries):
        queries(_queries) {}
};

// Bidir-BFS, with edge bit compression.
int (*BfsFuncPtr_Comp)(Operation&, int,
                int *, int *, BitState *, BitState *,
                int *[], int *[]);

int BidirBFS_Comp(Operation& query, int count,
                int *_visit, int *_rvisit, BitState *_comp, BitState *_rcomp,
                int *_points[2], int *_rpoints[2])
{
    if (query.e.u == query.e.v) return 0;
    int level = 0, rlevel = 0;
    int sz[2], rsz[2];
    memset(sz, 0, sizeof(sz)); memset(rsz, 0, sizeof(rsz));

    _points[0][sz[0]++] = query.e.u;
    _rpoints[0][rsz[0]++] = query.e.v;

    int base = query.e.u >> BIT_POW, rbase = query.e.v >> BIT_POW;
    _visit[base] = count; _comp[base] = ((BitState)1 << (query.e.u & BIT_MASK));
    _rvisit[rbase] = count; _rcomp[rbase] = ((BitState)1 << (query.e.v & BIT_MASK));

    while(sz[level & 1] != 0 && rsz[rlevel & 1] != 0)
    {
        int now = level & 1, next = now ^ 1;
        int rnow = rlevel & 1, rnext = rnow ^ 1;

        if (sz[now] <= rsz[rnow])
        {
            sz[next] = 0;
            // for (int i = sz[now] - 1; i >= 0; --i)
            for (int i = 0; i < sz[now]; ++i)
            {                
                int u = _points[now][i];
                BitNode *vpool = bitEdges.pool + bitEdges.start_pos[u];
                // for (int j = bitEdges.edge_num[u] - 1; j >= 0; --j)
                for (int j = 0; j < bitEdges.edge_num[u]; ++j)
                {
                    BitNode bn = vpool[j];
                    if (_rvisit[bn.base] == count &&
                        (_rcomp[bn.base] & bn.state) != 0)
                        return level + rlevel + 1;
                    if (_visit[bn.base] != count)
                    {
                        _visit[bn.base] = count;
                        _comp[bn.base] = bn.state;
                    }
                    else
                    {
                        bn.state = ((_comp[bn.base] ^ bn.state) & bn.state);
                        _comp[bn.base] |= bn.state;
                    }

                    int vhigh = (bn.base << BIT_POW);
                    while (bn.state)
                    {
                        int v = (vhigh | CTZ(bn.state));
                        _points[next][sz[next]++] = v;
                        bn.state &= (bn.state - 1);                        
                    }
                }

                // traverse adjacent edges in DeltaGraphS.
                if (dGraphS.batch_h[u] == dGraphS.batch_cnt)
                {
                    for (int ptr = dGraphS.head[u]; ptr != -1; ptr = dGraphS.next[ptr])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[ptr]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.end[ptr];
                            BitNode bn((v >> BIT_POW), ((BitState)1 << (v & BIT_MASK)));

                            if (_rvisit[bn.base] == count &&
                                (_rcomp[bn.base] & bn.state) != 0)
                                return level + rlevel + 1;

                            if (_visit[bn.base] != count)
                            {
                                _visit[bn.base] = count;
                                _comp[bn.base] = bn.state;
                                _points[next][sz[next]++] = v;
                            }
                            else if ((_comp[bn.base] & bn.state) == 0)
                            {
                                _comp[bn.base] |= bn.state;
                                _points[next][sz[next]++] = v;
                            }
                        }
                    }
                }
            }
            level++;
        }
        else
        {
            rsz[rnext] = 0;
            // for (int i = rsz[rnow] - 1; i >= 0; --i)
            for (int i = 0; i < rsz[rnow]; ++i)
            {
                int u = _rpoints[rnow][i];
                BitNode *vpool = bitEdges.rpool + bitEdges.rstart_pos[u];
                // for (int j = bitEdges.redge_num[u] - 1; j >= 0; --j)
                for (int j = 0; j < bitEdges.redge_num[u]; ++j)
                {
                    BitNode bn = vpool[j];
                    if (_visit[bn.base] == count &&
                        (_comp[bn.base] & bn.state) != 0)
                            return level + rlevel + 1;
                    if (_rvisit[bn.base] != count)
                    {
                        _rvisit[bn.base] = count;
                        _rcomp[bn.base] = bn.state;
                    }
                    else
                    {
                        bn.state = ((_rcomp[bn.base] ^ bn.state) & bn.state);
                        _rcomp[bn.base] |= bn.state;
                    } 

                    int vhigh = (bn.base << BIT_POW);
                    while (bn.state)
                    {
                        int v = (vhigh | CTZ(bn.state));
                        _rpoints[rnext][rsz[rnext]++] = v;
                        bn.state &= (bn.state - 1);                        
                    }             
                }

                // traverse adjacent redges in DeltaGraphS.
                if (dGraphS.batch_rh[u] == dGraphS.batch_cnt)
                {
                    for (int ptr = dGraphS.rhead[u]; ptr != -1; ptr = dGraphS.rnext[ptr])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[ptr]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.rend[ptr];
                            BitNode bn((v >> BIT_POW), ((BitState)1 << (v & BIT_MASK)));

                            if (_visit[bn.base] == count &&
                                (_comp[bn.base] & bn.state) != 0)
                                return level + rlevel + 1;

                            if (_rvisit[bn.base] != count)
                            {
                                _rvisit[bn.base] = count;
                                _rcomp[bn.base] = bn.state;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                            else if ((_rcomp[bn.base] & bn.state) == 0)
                            {
                                _rcomp[bn.base] |= bn.state;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                        }
                    }
                }
            }
            rlevel ++;
        }      
    }
    return -1;      
}

int BidirBFS_Comp_Deg(Operation& query, int count,
                int *_visit, int *_rvisit, BitState *_comp, BitState *_rcomp,
                int *_points[2], int *_rpoints[2])
{
    if (query.e.u == query.e.v) return 0;
    int level = 0, rlevel = 0;
    int sz[2], rsz[2];
    memset(sz, 0, sizeof(sz)); memset(rsz, 0, sizeof(rsz));
    int sum_deg = 0, rsum_deg = 0;

    _points[0][sz[0]++] = query.e.u;
    _rpoints[0][rsz[0]++] = query.e.v;

    int base = query.e.u >> BIT_POW, rbase = query.e.v >> BIT_POW;
    _visit[base] = count; _comp[base] = ((BitState)1 << (query.e.u & BIT_MASK));
    _rvisit[rbase] = count; _rcomp[rbase] = ((BitState)1 << (query.e.v & BIT_MASK));

    while(sz[level & 1] != 0 && rsz[rlevel & 1] != 0)
    {
        int now = level & 1, next = now ^ 1;
        int rnow = rlevel & 1, rnext = rnow ^ 1;

        if (sum_deg <= rsum_deg)
        {
            sz[next] = 0;
            // for (int i = sz[now] - 1; i >= 0; --i)
            for (int i = 0; i < sz[now]; ++i)
            {                
                int u = _points[now][i];
                BitNode *vpool = bitEdges.pool + bitEdges.start_pos[u];
                // for (int j = bitEdges.edge_num[u] - 1; j >= 0; --j)
                for (int j = 0; j < bitEdges.edge_num[u]; ++j)
                {
                    BitNode bn = vpool[j];
                    if (_rvisit[bn.base] == count &&
                        (_rcomp[bn.base] & bn.state) != 0)
                        return level + rlevel + 1;
                    if (_visit[bn.base] != count)
                    {
                        _visit[bn.base] = count;
                        _comp[bn.base] = bn.state;
                    }
                    else
                    {
                        bn.state = ((_comp[bn.base] ^ bn.state) & bn.state);
                        _comp[bn.base] |= bn.state;
                    }

                    int vhigh = (bn.base << BIT_POW);
                    while (bn.state)
                    {
                        int v = (vhigh | CTZ(bn.state));
                        _points[next][sz[next]++] = v;
                        bn.state &= (bn.state - 1);                        
                    }
                }

                // traverse adjacent edges in DeltaGraphS.
                if (dGraphS.batch_h[u] == dGraphS.batch_cnt)
                {
                    for (int ptr = dGraphS.head[u]; ptr != -1; ptr = dGraphS.next[ptr])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[ptr]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.end[ptr];
                            BitNode bn((v >> BIT_POW), ((BitState)1 << (v & BIT_MASK)));

                            if (_rvisit[bn.base] == count &&
                                (_rcomp[bn.base] & bn.state) != 0)
                                return level + rlevel + 1;

                            if (_visit[bn.base] != count)
                            {
                                _visit[bn.base] = count;
                                _comp[bn.base] = bn.state;
                                _points[next][sz[next]++] = v;
                            }
                            else if ((_comp[bn.base] & bn.state) == 0)
                            {
                                _comp[bn.base] |= bn.state;
                                _points[next][sz[next]++] = v;
                            }
                        }
                    }
                }
            }
            sum_deg = 0;
            for (int i = sz[next] - 1; i >= 0; --i)
                sum_deg += bitEdges.edge_num[_points[next][i]];
            level++;
        }
        else
        {
            rsz[rnext] = 0;
            // for (int i = rsz[rnow] - 1; i >= 0; --i)
            for (int i = 0; i < rsz[rnow]; ++i)
            {
                int u = _rpoints[rnow][i];
                BitNode *vpool = bitEdges.rpool + bitEdges.rstart_pos[u];
                // for (int j = bitEdges.redge_num[u] - 1; j >= 0; --j)
                for (int j = 0; j < bitEdges.redge_num[u]; ++j)
                {
                    BitNode bn = vpool[j];
                    if (_visit[bn.base] == count &&
                        (_comp[bn.base] & bn.state) != 0)
                            return level + rlevel + 1;
                    if (_rvisit[bn.base] != count)
                    {
                        _rvisit[bn.base] = count;
                        _rcomp[bn.base] = bn.state;
                    }
                    else
                    {
                        bn.state = ((_rcomp[bn.base] ^ bn.state) & bn.state);
                        _rcomp[bn.base] |= bn.state;
                    } 

                    int vhigh = (bn.base << BIT_POW);
                    while (bn.state)
                    {
                        int v = (vhigh | CTZ(bn.state));
                        _rpoints[rnext][rsz[rnext]++] = v;
                        bn.state &= (bn.state - 1);                        
                    }             
                }

                // traverse adjacent redges in DeltaGraphS.
                if (dGraphS.batch_rh[u] == dGraphS.batch_cnt)
                {
                    for (int ptr = dGraphS.rhead[u]; ptr != -1; ptr = dGraphS.rnext[ptr])
                    {
                        OpTimeStamp *time_vec = &dGraphS.time_pool[dGraphS.time_head[ptr]];
                        if (LegalV(time_vec, query.ts.time))
                        {
                            int v = dGraphS.rend[ptr];
                            BitNode bn((v >> BIT_POW), ((BitState)1 << (v & BIT_MASK)));

                            if (_visit[bn.base] == count &&
                                (_comp[bn.base] & bn.state) != 0)
                                return level + rlevel + 1;

                            if (_rvisit[bn.base] != count)
                            {
                                _rvisit[bn.base] = count;
                                _rcomp[bn.base] = bn.state;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                            else if ((_rcomp[bn.base] & bn.state) == 0)
                            {
                                _rcomp[bn.base] |= bn.state;
                                _rpoints[rnext][rsz[rnext]++] = v;
                            }
                        }
                    }
                }
            }
            rsum_deg = 0;
            for (int i = rsz[rnext] - 1; i >= 0 ; --i)
                rsum_deg += bitEdges.redge_num[_rpoints[rnext][i]];
            rlevel ++;
        }      
    }
    return -1;      
}

class ConcurrentQueryProcessor_Comp
{
    Operation *queries;

public:
    void operator() (const blocked_range<size_t>& r) const
    {
        for (size_t i=r.begin();i!=r.end();++i)
        {
            int pid;
            while (!idle_pid.try_pop(pid));

            ans[i] = (*BfsFuncPtr_Comp)(queries[i], visit_label[i],
                                    visit[pid], rvisit[pid], bit_state[pid], rbit_state[pid],
                                    points[pid], rpoints[pid]);
            idle_pid.push(pid);
        }
    }
    ConcurrentQueryProcessor_Comp(Operation *_queries): queries(_queries) {}
};

void Ready()
{
    puts("R");
    cout.flush();
}

int max_block_father_id;
void (*ProcessFuncPtr)();

void Process_Comp()
{
    static affinity_partitioner ap;
    
    // double bfs_time = 0;
    // struct timeval start1, end1;

    Ready();
    while (true)
    {
        if (op_list.readBatchOp() == 0) break;

        dGraphS.build(op_list.update, op_list.u_cnt);

        for (int i=0;i<op_list.u_cnt;++i)
            if (op_list.update[i].ts.op == 1)
                bitEdges.DeleteEdge(op_list.update[i].e);

        for (int i=0;i<op_list.q_cnt;++i)
            visit_label[i] = ++visit_label_count;

        // gettimeofday(&start1, NULL);
        
        parallel_for(blocked_range<size_t>(0, op_list.q_cnt),
            ConcurrentQueryProcessor_Comp(op_list.query), ap);

        // gettimeofday(&end1, NULL);
        // bfs_time += (end1.tv_sec - start1.tv_sec) + (end1.tv_usec - start1.tv_usec) / 1000000.0;        

        // only add these edges is enough.
        for (int i=0;i<dGraphS.add_edge_cnt;++i)
            bitEdges.AddEdge(dGraphS.add_edge[i]);

        for (int i=0;i<op_list.q_cnt;++i)
            printf("%d\n", ans[i]);
        cout.flush();
    }
    // fprintf(stderr, "bfs_time=%.2f\n", bfs_time * 1000);
}

void Process()
{    
    static affinity_partitioner ap;

    // double bfs_time = 0;
    // struct timeval start1, end1;

    Ready();
    while (true)
    {
        if (op_list.readBatchOp() == 0) break;

        dGraphS.build(op_list.update, op_list.u_cnt);

        for (int i=0;i<op_list.u_cnt;++i)
            if (op_list.update[i].ts.op == 1)
                DeleteEdge(op_list.update[i].e.u, op_list.update[i].e.v);

        for (int i=0;i<op_list.q_cnt;++i)
            visit_label[i] = ++visit_label_count;

        // gettimeofday(&start1, NULL);

        parallel_for(blocked_range<size_t>(0, op_list.q_cnt),
            ConcurrentQueryProcessor(op_list.query), ap);

        // gettimeofday(&end1, NULL);
        // bfs_time += (end1.tv_sec - start1.tv_sec) + (end1.tv_usec - start1.tv_usec) / 1000000.0;

        // only add these edges is enough.
        for (int i=0;i<dGraphS.add_edge_cnt;++i)
            AddNewEdge(dGraphS.add_edge[i].u, dGraphS.add_edge[i].v);

        for (int i=0;i<op_list.q_cnt;++i)
            printf("%d\n", ans[i]);
        cout.flush();

    }
    // fprintf(stderr, "bfs_time=%.2f\n", bfs_time * 1000);

}

const int RAND_QUERY_NUM = 1000000;
Operation *rand_queries;

void GenRandQueries()
{
    rand_queries = new Operation[RAND_QUERY_NUM];
    for (int i = 0; i < RAND_QUERY_NUM; ++i)
    {
        rand_queries[i].e.u = rand() % node_cnt;
        rand_queries[i].e.v = rand() % node_cnt;
        rand_queries[i].ts.time = 0;
    }
}

double top20p_deg_ratio;
double CalcDegreeDistribution()
{
    int *sorted_temp = new int[node_cnt];

    // check degree's 2-8 law.
    for (int i = 0; i < node_cnt ; ++i)
        sorted_temp[i] = out_deg[i] + in_deg[i];
    sort(sorted_temp, sorted_temp + node_cnt);
    double sum_top20p_deg = 0;
    for (int i = 0; i < node_cnt / 5; ++i)
        sum_top20p_deg += sorted_temp[node_cnt - i - 1]; 
    top20p_deg_ratio = sum_top20p_deg / (edge_cnt + redge_cnt);
    delete []sorted_temp;
    // cerr << "top20p_deg_ratio=" << top20p_deg_ratio << endl;
    return top20p_deg_ratio;
}

double CalcDegreeVariance()
{
    double avg_deg = (double)edge_cnt / node_cnt;
    double outdeg_variance = 0, indeg_variance = 0;
    for (int i=0;i<node_cnt;++i)
    {
        outdeg_variance += (out_deg[i] - avg_deg) * (out_deg[i] - avg_deg);
        indeg_variance += (in_deg[i] - avg_deg) * (in_deg[i] - avg_deg);
    }
    outdeg_variance /= node_cnt;
    indeg_variance /= node_cnt;

    // cerr << "deg_var=" << outdeg_variance << ", " << indeg_variance << endl;

    return outdeg_variance + indeg_variance;
}

int GetCentreCnt(Operation& query, int count,
                     int *_visit, int *_rvisit, int *_points[2], int *_rpoints[2],
                     int *_pre, int *_rpre, int *_centre_cnt)
{
    if (query.e.u == query.e.v) return 0;
    int level = 0, rlevel = 0;
    int sz[2], rsz[2];  
    memset(sz, 0, sizeof(sz)); memset(rsz, 0, sizeof(rsz));

    _points[0][sz[0]++] = query.e.u;
    _rpoints[0][rsz[0]++] = query.e.v;
    _visit[query.e.u] = count; _rvisit[query.e.v] = count;
    while(sz[level & 1] != 0 && rsz[rlevel & 1] != 0)
    {
        int now = level & 1, next = now ^ 1;
        int rnow = rlevel & 1, rnext = rnow ^ 1;

        if (sz[now] <= rsz[rnow])
        {
            sz[next] = 0;
            // for (int i = 0; i < sz[now]; ++i)
            for (int i = sz[now] - 1; i >= 0; --i)
            {
                int u = _points[now][i];
                for (int j = first[u]; j != -1; j = edges[j].next)
                {
                    int v = edges[j].to;
                    if (_visit[v] != count)
                    {
                        if (_rvisit[v] == count)
                        {
                            int cur = u;
                            while (cur != query.e.u)
                            {
                                _centre_cnt[cur]++;
                                cur = _pre[cur];
                            }
                            cur = v;
                            while (cur != query.e.v)
                            {
                                _centre_cnt[cur]++;
                                cur = _rpre[cur];
                            }
                            return level + rlevel + 1;
                        }
                        _visit[v] = count;
                        _points[next][sz[next]++] = v;
                        _pre[v] = u;                
                    }
                }
            }
            level ++;
        }
        else
        {
            rsz[rnext] = 0;
            // for (int i = 0; i < rsz[rnow]; ++i)
            for (int i = rsz[rnow] - 1; i >= 0; --i)
            {
                int u = _rpoints[rnow][i];
                for (int j = rfirst[u]; j != -1; j = redges[j].next)
                {
                    int v = redges[j].to;
                    if (_rvisit[v] != count)
                    {
                        if (_visit[v] == count)
                        {
                            int cur = u;
                            while (cur != query.e.v)
                            {
                                _centre_cnt[cur]++;
                                cur = _rpre[cur];                                
                            }
                            cur = v;
                            while (cur != query.e.u)
                            {
                                _centre_cnt[cur]++;
                                cur = _pre[cur];                                 
                            }
                            return level + rlevel + 1;
                        }
                        _rvisit[v] = count;
                        _rpoints[rnext][rsz[rnext]++] = v;
                        _rpre[v] = u;
                    }
                }
            }
            rlevel ++;
        }
    }
    return -1;
}

vector<pair<int, int>> edge_vec;

int *pre[THREADNUM], *rpre[THREADNUM];
int *pre_mem_pool, *rpre_mem_pool;
int *centre_cnt[THREADNUM], *sum_centre_cnt;
int *centre_cnt_mem_pool;

class ConcurrentGetCentreCnt
{
    Operation *queries;

public:
    void operator() (const blocked_range<size_t>& r) const
    {
        for (size_t i=r.begin();i!=r.end();++i)
        {
            int pid;
            while (!idle_pid.try_pop(pid));
            GetCentreCnt(queries[i], visit_label[i],
                            visit[pid], rvisit[pid], points[pid], rpoints[pid],
                            pre[pid], rpre[pid], centre_cnt[pid]);           
            idle_pid.push(pid);
        }
    }
    ConcurrentGetCentreCnt(Operation *_queries):
        queries(_queries) {}
};

void CalcCentrality()
{
    pre_mem_pool = new int[THREADNUM * MAXNODECOUNT];
    rpre_mem_pool = new int[THREADNUM * MAXNODECOUNT];
    centre_cnt_mem_pool = new int[THREADNUM * MAXNODECOUNT];
    memset(centre_cnt_mem_pool, 0, sizeof(int) * THREADNUM * MAXNODECOUNT);
    for (int i=0;i<THREADNUM;++i)
    {
        pre[i] = pre_mem_pool + (i * MAXNODECOUNT);
        rpre[i] = rpre_mem_pool + (i * MAXNODECOUNT);
        centre_cnt[i] = centre_cnt_mem_pool + (i * MAXNODECOUNT);
    } 
    sum_centre_cnt = new int[MAXNODECOUNT]; 
    memset(sum_centre_cnt, 0, sizeof(int) * MAXNODECOUNT);
    
    int calc_centrality_query_num = 5000;
    for (int i = 0; i < calc_centrality_query_num; ++i)
        visit_label[i] = ++visit_label_count;

    parallel_for(blocked_range<size_t>(0, calc_centrality_query_num),
        ConcurrentGetCentreCnt(rand_queries));
    for (int i = 0; i < THREADNUM; ++i)
        for (int j = 0; j < node_cnt; ++j)
            sum_centre_cnt[j] += centre_cnt[i][j];

    delete []pre_mem_pool;
    delete []rpre_mem_pool;
    delete []centre_cnt_mem_pool;
}

// const int TEST_BATCH_SIZE = 5000;
const int TEST_BATCH_SIZE = 500;
double TryOriginGraphEfficiency(int& test_query_cnt)
{
    int warmup_query_num = 2000;
    for (int i = 0; i < warmup_query_num; ++i)
        visit_label[i] = ++visit_label_count;
    parallel_for(blocked_range<size_t>(0, warmup_query_num),
        ConcurrentQueryProcessor(rand_queries));

    struct timeval start1, end1;
    double bfs_org_rand_time = 0;

    while (bfs_org_rand_time < 500.0 &&
            test_query_cnt + TEST_BATCH_SIZE <= RAND_QUERY_NUM)
    {
        for (int i = 0; i < TEST_BATCH_SIZE; ++i)
            visit_label[i] = ++visit_label_count;

        gettimeofday(&start1, NULL);
            
        parallel_for(blocked_range<size_t>(0, TEST_BATCH_SIZE),
            ConcurrentQueryProcessor(rand_queries + test_query_cnt));

        gettimeofday(&end1, NULL);
        bfs_org_rand_time += ((end1.tv_sec - start1.tv_sec) + (end1.tv_usec - start1.tv_usec) / 1000000.0) * 1000.0;
        test_query_cnt += TEST_BATCH_SIZE;
    }

    // fprintf(stderr, "bfs_org_rand_time=%.2f\n", bfs_org_rand_time);

    return bfs_org_rand_time;
}

double TryCompressionGraphEfficiency(int *new_vertex_id, int test_query_cnt)
{
    Operation *new_id_rand_queries = new Operation[RAND_QUERY_NUM];
    for (int i = 0; i < RAND_QUERY_NUM; ++i)
    {
        new_id_rand_queries[i].e.u = new_vertex_id[rand_queries[i].e.u];
        new_id_rand_queries[i].e.v = new_vertex_id[rand_queries[i].e.v];
        new_id_rand_queries[i].ts.time = 0;
    }

    int warmup_query_num = 2000;

    for (int i = 0; i < warmup_query_num; ++i)
        visit_label[i] = ++visit_label_count;
    parallel_for(blocked_range<size_t>(0, warmup_query_num),
        ConcurrentQueryProcessor_Comp(new_id_rand_queries));
    
    struct timeval start1, end1;
    double bfs_comp_rand_time = 0;

    int test_query_num = 0;
    while (test_query_num < test_query_cnt)
    {
        for (int i = 0; i < TEST_BATCH_SIZE; ++i)
            visit_label[i] = ++visit_label_count;

        gettimeofday(&start1, NULL);
            
        parallel_for(blocked_range<size_t>(0, TEST_BATCH_SIZE),
            ConcurrentQueryProcessor_Comp(new_id_rand_queries + test_query_num));

        gettimeofday(&end1, NULL);
        bfs_comp_rand_time += ((end1.tv_sec - start1.tv_sec) + (end1.tv_usec - start1.tv_usec) / 1000000.0) * 1000.0;
        test_query_num += TEST_BATCH_SIZE;  
    }

    // fprintf(stderr, "bfs_comp_rand_time=%.2f\n", bfs_comp_rand_time);

    delete []new_id_rand_queries;
    return bfs_comp_rand_time;
}

bool vertex_outdeg_desc_cmp(const int& a, const int& b)
{
    if (out_deg[a] == out_deg[b])
        return a < b;
    return out_deg[a] > out_deg[b];
}
bool vertex_outdeg_asc_cmp(const int& a, const int& b)
{
    if (out_deg[a] == out_deg[b])
        return a < b;
    return out_deg[a] < out_deg[b];
}
bool vertex_indeg_asc_cmp(const int& a, const int& b)
{
    if (in_deg[a] == in_deg[b])
        return a < b;
    return in_deg[a] < in_deg[b];
}
bool vertex_indeg_desc_cmp(const int& a, const int& b)
{
    if (in_deg[a] == in_deg[b])
        return a < b;
    return in_deg[a] > in_deg[b];
}

bool vertex_centre_cmp(const int& a, const int& b)
{
    if (sum_centre_cnt[a] == sum_centre_cnt[b])
        return a < b;
    return sum_centre_cnt[a] > sum_centre_cnt[b];
}

void GenRandQueries2()
{
    int *vertex_temp_centre = new int[node_cnt];
    for (int i = 0; i < node_cnt; ++i) vertex_temp_centre[i] = i;
    sort(vertex_temp_centre, vertex_temp_centre + node_cnt, vertex_centre_cmp);
    
    int *vertex_temp_outdeg = new int[node_cnt];
    for (int i = 0; i < node_cnt; ++i) vertex_temp_outdeg[i] = i;
    sort(vertex_temp_outdeg, vertex_temp_outdeg + node_cnt, vertex_outdeg_desc_cmp);

    int *vertex_temp_indeg = new int[node_cnt];
    for (int i = 0; i < node_cnt; ++i) vertex_temp_indeg[i] = i;
    sort(vertex_temp_indeg, vertex_temp_indeg + node_cnt, vertex_indeg_desc_cmp);

    int big_node_cnt = min(node_cnt, 1000);

    for (int i = 0; i < RAND_QUERY_NUM; ++i)
    {
        int r = i % 3;
        if (r == 0)
        {
            rand_queries[i].e.u = rand() % node_cnt;
            rand_queries[i].e.v = rand() % node_cnt;                      
        }
        else if (r == 1)
        {
            rand_queries[i].e.u = vertex_temp_centre[rand() % big_node_cnt];
            rand_queries[i].e.v = vertex_temp_centre[rand() % big_node_cnt];           
        }
        else
        {
            rand_queries[i].e.u = vertex_temp_outdeg[rand() % big_node_cnt];
            rand_queries[i].e.v = vertex_temp_indeg[rand() % big_node_cnt];           
        }
        rand_queries[i].ts.time = 0; 
    }
    delete []vertex_temp_centre;
    delete []vertex_temp_outdeg;
    delete []vertex_temp_indeg;
}

void BFS_Reassign_VertexId(int s, int& idx, int * new_vertex_id)
{
    queue<int>que;
    que.push(s);
    new_vertex_id[s] = idx++;

    while (!que.empty())
    {
        int u = que.front(); que.pop();
        for (int i = first[u]; i != -1; i = edges[i].next)
        {
            int v = edges[i].to;
            if (new_vertex_id[v] == -1)
            {
                new_vertex_id[v] = idx++;
                que.push(v);
            }
        }
    }
}

int* Naive_Reorder()
{
    int *new_vertex_id = new int[node_cnt];
    memset(new_vertex_id, -1, sizeof(int) * node_cnt);
    int *vertex_temp = new int[node_cnt];
    for (int i = 0; i < node_cnt; ++i) vertex_temp[i] = i;
    sort(vertex_temp, vertex_temp + node_cnt, vertex_outdeg_desc_cmp);

    int u, idx = 0;
    for (int i = 0; i < node_cnt; ++i)
    {
        int u = vertex_temp[i];
        if (new_vertex_id[u] == -1)
            BFS_Reassign_VertexId(u, idx, new_vertex_id);
    }

    return new_vertex_id;
}

void RCM_BFS(int s, int& idx, int *new_vertex_id, char *inq)
{
    queue<int>que;
    vector<int> adj_nodes;
    que.push(s);    
    inq[s] = 1;

    while (!que.empty())
    {
        int u = que.front(); que.pop();
        new_vertex_id[u] = idx++;
        adj_nodes.clear();
        for (int i = first[u]; i != -1; i = edges[i].next)
        {
            int v = edges[i].to;
            if (new_vertex_id[v] == -1)
                adj_nodes.push_back(v);
        }
        // sort(adj_nodes.begin(), adj_nodes.end(), vertex_outdeg_asc_cmp);
        sort(adj_nodes.begin(), adj_nodes.end(), vertex_outdeg_desc_cmp);
        for (int i = 0; i < adj_nodes.size(); ++i)
            if (inq[adj_nodes[i]] == 0)
            {
                que.push(adj_nodes[i]);
                inq[adj_nodes[i]] = 1;
            }   
    }    
}

int* RCM_Reorder()
{
    int *new_vertex_id = new int[node_cnt];
    memset(new_vertex_id, -1, sizeof(int) * node_cnt);
    int *vertex_temp = new int[node_cnt];
    for (int i = 0; i < node_cnt; ++i) vertex_temp[i] = i;
    // sort(vertex_temp, vertex_temp + node_cnt, vertex_outdeg_asc_cmp);
    sort(vertex_temp, vertex_temp + node_cnt, vertex_outdeg_desc_cmp);
    
    char *inq = new char[node_cnt];
    memset(inq, 0, sizeof(char) * node_cnt);
    int u, idx = 0;

    // for (int i = 0; i < node_cnt; ++i)
    // {
    //     u = vertex_temp[i];
    //     if (out_deg[u] <= 2)
    //     new_vertex_id[u] = idx++;
    // }
    for (int i = 0; i < node_cnt; ++i)
    {
        u = vertex_temp[i];
        if (new_vertex_id[u] == -1)
            RCM_BFS(u, idx, new_vertex_id, inq);
    }
    delete []inq;

    // for (int i = 0; i < node_cnt; ++i)
    //     new_vertex_id[i] = node_cnt - new_vertex_id[i] - 1;

    return new_vertex_id;
}

void ReorderOriginGraph()
{
    int *new_vertex_id = Naive_Reorder();
    // int *new_vertex_id = RCM_Reorder();        

    for (auto iter = node_id.begin(); iter != node_id.end(); ++iter)
    {
        int orgid = iter->first, interid = iter->second;
        node_id[orgid] = new_vertex_id[interid];
    }
    // also update edge_vec's id by new id.
    for (int i = 0; i < edge_vec.size(); ++i)
    {
        edge_vec[i].first = new_vertex_id[edge_vec[i].first];
        edge_vec[i].second = new_vertex_id[edge_vec[i].second];
    }

    GraphInit();

    sort(edge_vec.begin(), edge_vec.end(), edge_cmp);
    for(int i = 0; i < edge_vec.size(); ++i)
    {
        int u = edge_vec[i].first;
        int v = edge_vec[i].second;
        AddOriginalEdge(u, v);
    }
    sort(edge_vec.begin(), edge_vec.end(), redge_cmp);
    for(int i = 0; i < edge_vec.size(); ++i)
    {
        int u = edge_vec[i].first;
        int v = edge_vec[i].second;
        AddReverseEdge(u, v);
    }

    delete []new_vertex_id;  
}

bool edge_deg_cmp(const pair<int, int>& a, const pair<int, int>& b)
{
    if (in_deg[a.second] == in_deg[b.second])
    {
        if (a.second == b.second)
            return in_deg[a.first] > in_deg[b.first];
        else
            return a.second < b.second;
    }
    return in_deg[a.second] > in_deg[b.second];
}

bool TryBitCompression()
{

    vector<pair<int, int>> new_edge_vec;
    int *new_vertex_id = new int[MAXNODECOUNT];
    memset(new_vertex_id, -1, sizeof(int) * MAXNODECOUNT);
    
    // generate new id to increase edge compression ratio.
    int u, v, idx = 0;

    sort(edge_vec.begin(), edge_vec.end(), edge_deg_cmp);    

    for (auto iter = edge_vec.begin(); iter != edge_vec.end(); ++iter)
    {
        if (new_vertex_id[iter->second] == -1)        
            new_vertex_id[iter->second] = idx++;
        if (new_vertex_id[iter->first] == -1)
            new_vertex_id[iter->first] = idx++;
        u = new_vertex_id[iter->first]; v = new_vertex_id[iter->second];
        new_edge_vec.push_back(make_pair(u,v));
    }
    
    bitEdges.init(new_edge_vec);


    // collect graph data features.
    int sum_comp_deg = 0, rsum_comp_deg = 0;
    double sum_centrality = 0, sum_comp_centrality_deg = 0, rsum_comp_centrality_deg = 0;
    for (int i=0;i<node_cnt;++i)
    {
        int u = new_vertex_id[i];
        sum_comp_deg += bitEdges.edge_num[u];
        rsum_comp_deg += bitEdges.redge_num[u];
        sum_centrality += sum_centre_cnt[i];
        
        if (bitEdges.edge_num[u] != 0)
            sum_comp_centrality_deg += (double)bitEdges.edge_num[u] / out_deg[i] * sum_centre_cnt[i];
        if (bitEdges.redge_num[u] != 0)
            rsum_comp_centrality_deg += (double)bitEdges.redge_num[u] / in_deg[i] * sum_centre_cnt[i];
    }
    double comp_ratio = (double)sum_comp_deg / edge_cnt;
    double rcomp_ratio = (double)rsum_comp_deg / edge_cnt;
    double comp_centrality_ratio = sum_comp_centrality_deg / sum_centrality;
    double rcomp_centrality_ratio = rsum_comp_centrality_deg / sum_centrality;
    
    // fprintf(stderr, "comp_deg=%d, %d comp_ratio=%.3f, %.3f\n", sum_comp_deg, rsum_comp_deg, comp_ratio, rcomp_ratio);


    int test_query_cnt = 0;
    double org_query_time = TryOriginGraphEfficiency(test_query_cnt);
    double comp_query_time = TryCompressionGraphEfficiency(new_vertex_id, test_query_cnt);
    // cerr << "test_query_cnt=" << test_query_cnt << endl;
    

    // if (org_query_time <= comp_query_time)
    if (top20p_deg_ratio < 0.5) // predict whether using bit compression runs faster here.

    {
        delete[]new_vertex_id;        
        return false;
    }
    
    // update orgid2vertexid map by new id.
    for (auto iter = node_id.begin(); iter != node_id.end(); ++iter)
    {
        int orgid = iter->first, interid = iter->second;
        node_id[orgid] = new_vertex_id[interid];
    }
    // also update edge_vec's id by new id.
    for (int i = 0; i < edge_vec.size(); ++i)
    {
        edge_vec[i].first = new_vertex_id[edge_vec[i].first];
        edge_vec[i].second = new_vertex_id[edge_vec[i].second];
    }
    // also update in_deg and out_deg.
    memset(out_deg, 0, sizeof(int) * MAXNODECOUNT);
    memset(in_deg, 0, sizeof(int) * MAXNODECOUNT);
    for (int i = 0; i < edge_vec.size(); ++i)
    {
        out_deg[edge_vec[i].first]++;
        in_deg[edge_vec[i].second]++;
    }

    delete[]new_vertex_id;
    return true;    
}


void ReadInit()
{    
    uint32_t orgu, orgv;
    int u, v;
    for(;;)
    {
        if (fastscan(orgu) == 0) break; fastscan(orgv);
        u = GetNodeId(orgu); v = GetNodeId(orgv);
        edge_vec.push_back(make_pair(u, v));
    }
    
    sort(edge_vec.begin(), edge_vec.end(), edge_cmp);
    for(int i = 0; i < edge_vec.size(); ++i)
    {
        u = edge_vec[i].first;
        v = edge_vec[i].second;
        AddOriginalEdge(u, v);
    }
    sort(edge_vec.begin(), edge_vec.end(), redge_cmp);
    for(int i = 0; i < edge_vec.size(); ++i)
    {
        u = edge_vec[i].first;
        v = edge_vec[i].second;
        AddReverseEdge(u, v);
    }
}

void WarmUpCache()
{
    int warmup_query_num = 5000;
    // int warmup_query_num = 2000;
    for (int i = 0; i < warmup_query_num; ++i)
        visit_label[i] = ++visit_label_count;

    if (is_bit_comp_open)
        parallel_for(blocked_range<size_t>(0, warmup_query_num),
            ConcurrentQueryProcessor_Comp(rand_queries));
    else
        parallel_for(blocked_range<size_t>(0, warmup_query_num),
            ConcurrentQueryProcessor(rand_queries));   
}

void Preprocess()
{
    GenRandQueries();
    
    CalcDegreeDistribution();
    double degree_invariance = CalcDegreeVariance();
    CalcCentrality();

    GenRandQueries2();   

    if (degree_invariance < 1000.0)
    {
        BfsFuncPtr = &BidirBFS;
        BfsFuncPtr_Comp = &BidirBFS_Comp;
    }
    else
    {
        BfsFuncPtr = &BidirBFS_Deg;
        BfsFuncPtr_Comp = &BidirBFS_Comp_Deg;
    }

    is_bit_comp_open = TryBitCompression();
    // cerr <<"is_bit_comp_open=" << is_bit_comp_open << endl;
    
    if (is_bit_comp_open)
        ProcessFuncPtr = &Process_Comp;
    else
        ProcessFuncPtr = &Process;

    WarmUpCache();
}

int main(void)
{
    tbb::task_scheduler_init init(THREADNUM);
    for (int i=0;i<THREADNUM;++i)
        idle_pid.push(i); 
    AllocBfsMem();
    GraphInit();
    ReadInit();
    ReorderOriginGraph();
    // std::cerr <<"Node num  " << node_cnt << endl;
    // std::cerr <<"Edge num  " << edge_cnt << endl;
    Preprocess();
    (*ProcessFuncPtr)(); 
   
    return 0;
}