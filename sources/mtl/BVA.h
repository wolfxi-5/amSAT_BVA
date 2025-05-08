/******************************************************************************************[BVA.h]
Copyright (c) 2023

**************************************************************************************************/

#ifndef Minisat_BVA_h
#define Minisat_BVA_h

#include <vector>
#include <map>
#include <unordered_set>

#include "core/SolverTypes.h"
#include "mtl/Sort.h"
#include "mtl/Vec.h"
#include "../archives/eigen-3.4.0/Eigen/SparseCore"

namespace Minisat {

class BVA {
public:
    bool open_bva = true;

    int num_vars;
    int num_clauses;

    int total_deleted; // 总删除数
    int cur_deleted;   // 当前轮次删除数

    int cur_reduce;
    int cur_restart;
    
    std::vector<std::vector<CRef>> *lit_to_clauses;
    std::vector<int> *lit_count_adjust;
    int adjacency_matrix_width;
    std::vector<Eigen::SparseVector<int>> adjacency_matrix;
    std::map<int, int> tmp_heuristic_cache_full;    

    std::vector<int> *matched_lits;                 // 0 存储选定的文字 lit
    std::vector<CRef> *matched_clauses;              // 0 存储交集子句 clause_idx
    std::vector<int> *matched_clauses_id;           // 0 存储子句索引位置 i
    std::vector<CRef> *matched_clauses_swap;         // 0 中间变量，用于更新（matched_clauses）
    std::vector<int> *matched_clauses_id_swap;      // 0 中间变量，用于更新（matched_clauses_id）

    std::vector<std::tuple<int, CRef, int>> *matched_entries;    // 0 中间变量，存储可能的交集子句（lit，other_idx，i）
    std::vector<int> *matched_entries_lits;                     // 0 中间变量，存储可能的文字 lit

    std::unordered_set<int> lits_to_update;                  // 0 存储哪些文字需要更新
    std::vector<std::tuple<CRef, int>> *clauses_to_remove;    // 0 存储（clause_idx，i）
    std::vector<Lit> *diff;                                  // 0 存储两个子句的差集

public:
    // 构造函数
    BVA() {      
        total_deleted = 0;
        cur_deleted = 0;

        cur_reduce = 1;
        cur_restart = 0;

        matched_lits = new std::vector<int>();
        matched_clauses = new std::vector<CRef>();
        matched_clauses_id = new std::vector<int>();
        matched_clauses_swap = new std::vector<CRef>();
        matched_clauses_id_swap = new std::vector<int>();
        matched_lits->reserve(2000);
        matched_clauses->reserve(2000);
        matched_clauses_swap->reserve(2000);
        matched_clauses_id->reserve(2000);
        matched_clauses_id_swap->reserve(2000);

        matched_entries = new std::vector<std::tuple<int, CRef, int>>();
        matched_entries_lits = new std::vector<int>();
        matched_entries->reserve(2000);
        matched_entries_lits->reserve(2000);   

        clauses_to_remove = new std::vector<std::tuple<CRef, int>>();
        diff = new std::vector<Lit>(); 
        lits_to_update.reserve(2000);
        clauses_to_remove->reserve(2000);
        diff->reserve(100);

        lit_to_clauses = nullptr;
        lit_count_adjust = nullptr;

        // printf("constructor\n");
    }

    ~BVA() {
        delete matched_lits;
        delete matched_clauses;
        delete matched_clauses_id;
        delete matched_clauses_swap;
        delete matched_clauses_id_swap;

        delete matched_entries;
        delete matched_entries_lits;  

        delete clauses_to_remove;
        delete diff; 

        delete lit_to_clauses;
        delete lit_count_adjust;
    }

    BVA(const BVA &bva) {
        open_bva = bva.open_bva;
        num_vars = bva.num_vars;
        num_clauses = bva.num_clauses;
        total_deleted = bva.total_deleted;

        lit_to_clauses = new std::vector<std::vector<CRef>>(*bva.lit_to_clauses);
        lit_count_adjust = new std::vector<int>(*bva.lit_count_adjust);

        adjacency_matrix_width = bva.adjacency_matrix_width;
        adjacency_matrix = bva.adjacency_matrix;
        tmp_heuristic_cache_full = bva.tmp_heuristic_cache_full;

        matched_lits = new std::vector<int>(*bva.matched_lits);
        matched_clauses = new std::vector<CRef>(*bva.matched_clauses);
        matched_clauses_id = new std::vector<int>(*bva.matched_clauses_id);
        matched_clauses_swap = new std::vector<CRef>(*bva.matched_clauses_swap);
        matched_clauses_id_swap = new std::vector<int>(*bva.matched_clauses_id_swap);

        matched_entries = new std::vector<std::tuple<int, CRef, int>>(*bva.matched_entries);
        matched_entries_lits = new std::vector<int>(*bva.matched_entries_lits);

        clauses_to_remove = new std::vector<std::tuple<CRef, int>>(*bva.clauses_to_remove);
        diff = new std::vector<Lit>(*bva.diff);
        lits_to_update = bva.lits_to_update;

        // printf("copy constructor\n");
    }

    void init(int vars, int clauses) {
        num_vars = vars;
        num_clauses = clauses;

        cur_deleted = 0;

        if (lit_to_clauses == nullptr) {
            lit_to_clauses = new std::vector<std::vector<CRef>>(num_vars * 2);
        } else {
            lit_to_clauses->clear();
            lit_to_clauses->resize(num_vars * 2);
        }

        if (lit_count_adjust == nullptr) {
            lit_count_adjust = new std::vector<int>(num_vars * 2);
        } else {
            lit_count_adjust->clear();
            lit_count_adjust->resize(num_vars * 2);
        }

        adjacency_matrix_width = num_vars * 4;
        adjacency_matrix.clear();
        adjacency_matrix.resize(num_vars);

        // lits_to_update.clear();
    }

    // * 相关函数
    inline uint32_t lit_idx(int32_t lit) { return (lit > 0 ? lit * 2 - 2 : -lit * 2 - 1); }    // 将一个文字转换为一个索引 (0 ~ 2*n-1)
    inline uint32_t sparsevec_lit_idx(int32_t lit) { return (lit > 0 ? lit - 1: -lit - 1); }   // 将一个文字转换为稀疏向量的索引 (0 ~ n-1)
    inline uint32_t sparsevec_lit_for_idx(int32_t lit) { return (lit + 1); }                   // 将稀疏向量的索引转换回文字

    inline int reduction(int lits_num, int clauses_num) { return (lits_num * clauses_num) - (lits_num + clauses_num); } // 计算BVA的子句化简数量
    inline int real_lit_count(int lit) { return lit_to_clauses->operator[](lit_idx(lit)).size() + lit_count_adjust->operator[](lit_idx(lit)); }

    void update_adjacency_matrix(ClauseAllocator &ca, int lit) {
        if (adjacency_matrix[sparsevec_lit_idx(lit)].nonZeros() > 0) return;

        Eigen::SparseVector<int> eigen(adjacency_matrix_width);

        for (CRef cr : (*lit_to_clauses)[lit_idx(lit)]) {
            Clause &cla = ca[cr];
            if (cla.mark() == 1) continue;
            for (int i = 0; i < cla.size(); i++) {
                int vabs = var(cla[i]);
                eigen.coeffRef(vabs) += 1;
            }
        }

        for (CRef cr : (*lit_to_clauses)[lit_idx(-lit)]) {
            Clause &cla = ca[cr];
            if (cla.mark() == 1) continue;
            for (int i = 0; i < cla.size(); i++) {
                int vabs = var(cla[i]);
                eigen.coeffRef(vabs) += 1;
            }
        }

        adjacency_matrix[sparsevec_lit_idx(lit)] = eigen;
    }
    
    int tiebreaking_heuristic(ClauseAllocator &ca, int lit1, int lit2) {
        if (tmp_heuristic_cache_full.find(sparsevec_lit_idx(lit2)) != tmp_heuristic_cache_full.end()) 
            return tmp_heuristic_cache_full[sparsevec_lit_idx(lit2)];
        
        update_adjacency_matrix(ca, lit1);
        update_adjacency_matrix(ca, lit2);

        Eigen::SparseVector<int> *vec1 = &adjacency_matrix[sparsevec_lit_idx(lit1)];
        Eigen::SparseVector<int> *vec2 = &adjacency_matrix[sparsevec_lit_idx(lit2)];

        int total_count = 0;
        for (int *varPtr = vec2->innerIndexPtr(); varPtr < vec2->innerIndexPtr() + vec2->nonZeros(); varPtr++) {
            int var = sparsevec_lit_for_idx(*varPtr);
            int count = vec2->coeffRef(sparsevec_lit_idx(var));
            update_adjacency_matrix(ca, var);
            Eigen::SparseVector<int> *vec3 = &adjacency_matrix[sparsevec_lit_idx(var)];
            total_count += count * vec3->dot(*vec1);
        }
        tmp_heuristic_cache_full[sparsevec_lit_idx(lit2)] = total_count;
        return total_count;
    }

    Lit least_frequent_not(const Clause &cla, Lit var) {
        Lit lmin = lit_Undef;
        int lmin_count = 0;
        
        for (int i = 0; i < cla.size(); i++) {
            Lit lit = cla[i];
            if (lit == var) continue;
            int count = lit_to_clauses->operator[](toInt(lit)).size() + lit_count_adjust->operator[](toInt(lit));
            if (lmin == lit_Undef || count < lmin_count) {
                lmin = lit;
                lmin_count = count;
            } 
        }
        return lmin;
    }

    void clause_sub(const Clause &cla, const Clause &other, int max_diff) {
        diff->resize(0);
        int idx_a = 0, idx_b = 0;

        while (idx_a < cla.size() && idx_b < other.size() && max_diff >= (int) diff->size()) {
            if (cla[idx_a] == other[idx_b]) {
                idx_a++;
                idx_b++;
            } else if (cla[idx_a] < other[idx_b]) {
                diff->push_back(cla[idx_a]);
                idx_a++;
            } else {
                idx_b++;
            }
        }

        while (idx_a < cla.size() && max_diff >= (int) diff->size()) {
            diff->push_back(cla[idx_a]);
            idx_a++;
        }
    }

    void clause_sub(const vec<Lit> &cla, const vec<Lit> &other, int max_diff) {
        diff->resize(0);
        int idx_a = 0, idx_b = 0;

        while (idx_a < cla.size() && idx_b < other.size() && max_diff >= (int) diff->size()) {
            if (cla[idx_a] == other[idx_b]) {
                idx_a++;
                idx_b++;
            } else if (cla[idx_a] < other[idx_b]) {
                diff->push_back(cla[idx_a]);
                idx_a++;
            } else {
                idx_b++;
            }
        }

        while (idx_a < cla.size() && max_diff >= (int) diff->size()) {
            diff->push_back(cla[idx_a]);
            idx_a++;
        }
    }

};


}
#endif