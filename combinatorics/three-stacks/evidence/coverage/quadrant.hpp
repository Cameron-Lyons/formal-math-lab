#pragma once
#include <array>
#include <bit>
#include <cstdint>
#include <stdexcept>

// At a fixed cut, the dual prefix order depends only on the high-card
// subsequence. The order and value set of its positive suffix depend only
// on the low-card subsequence and its positions. Positional and value-order
// contributions to the two ranks can therefore be accumulated separately.
namespace quadrant {
template<int N,int K> struct Encoder {
    static constexpr int M=N-1-K;
    std::array<unsigned,K> prefix_value{},head_weight{},tail_weight{};
    unsigned low_positions_fixed=0,high_values=0,low_values=0;
    int head_base=0,tail_base=0,low_count=0;
    std::array<unsigned,K+1> factorial{};
    // prefix_values are sorted, suffix comprises M positive values then zero.
    Encoder(const int *prefix_values,const int *suffix){
        factorial[0]=1;for(int i=1;i<=K;i++)factorial[i]=factorial[i-1]*i;
        for(int i=0;i<K;i++){
            unsigned v=prefix_values[i];prefix_value[i]=v;
            if(v>M){
                high_values|=1u<<i;head_weight[i]=factorial[v-M-1];
            }else{
                low_values|=1u<<i;++low_count;
                tail_weight[i]=factorial[M]/factorial[M+1-v];
            }
        }
        unsigned high_after=0,low_before=0;
        for(int i=0;i<K;i++) if(prefix_value[i]<=M)low_before|=1u<<prefix_value[i];
        for(int j=M-1;j>=0;j--){
            unsigned v=suffix[j];
            if(v>M){
                head_base+=factorial[v-M-1]*std::popcount(high_after&((1u<<v)-1));
                high_after|=1u<<v;
            }
        }
        for(int i=0;i<K;i++)if(prefix_value[i]>M)
            head_base+=head_weight[i]*std::popcount(high_after&((1u<<prefix_value[i])-1));
        for(int j=0;j<M;j++){
            unsigned v=suffix[j];
            if(v<=M){
                tail_base+=(factorial[M]/factorial[M+1-v])*std::popcount(low_before>>v);
                low_before|=1u<<v;
                low_positions_fixed|=1u<<(N-2-K-j);
            }
        }
    }
    struct Key{unsigned head, order, set;};
    template<class T> Key key(const T* word) const{
        unsigned high=high_values,low=0,set=low_positions_fixed,h=head_base,t=tail_base;
        for(int i=0;i<K;i++){
            unsigned v=word[i];
            if(int(v)>=low_count){
                h+=head_weight[v]*std::popcount(high&((1u<<v)-1));
                high^=1u<<v;
            }else{
                t+=tail_weight[v]*std::popcount(low>>v);
                low|=1u<<v;set|=1u<<(N-2-i);
            }
        }
        return {h,t,set};
    }
};
}
