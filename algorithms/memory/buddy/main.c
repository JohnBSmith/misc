
// Buddy memory allocator

#include <stdlib.h>
#include <stdio.h>

struct node{
    struct node* next;
};

struct free_list{
    struct node* first;
};

typedef struct node node;
typedef struct free_list free_list;

// 257*2^8
char mem[257*256];
int imax = 8;
free_list free_tab[9];

int exp2i(int n){
    return 1<<n;
}

void print_free_tab(){
    node* p;
    int i;
    for(i = imax; i>=0; i--){
        printf("%.2i|",i);
        for(p = free_tab[i].first; p!=0; p = p->next){
            printf("*");
        }
        printf("\n");
    }
}

int bsize(void* p){
    return *((char*)p-1);
}

int getindex(int n){
    int i,k;
    i = 256;
    k = 0;
    while(1){
        if(n<=i) return k;
        i*=2;
        k++;
    }
}

void append(free_list* a, node* p1){
    node* p = a->first;
    if(p==0){
        a->first = p1;
    }else{
        while(p->next!=0) p = p->next;
        p->next = p1;
    }
    p1->next = 0;
}

node* getn(int n){
    if(n>imax) return 0;
    node* p = free_tab[n].first;
    if(p==0){
        p = getn(n+1);
        if(p!=0){
            append(&free_tab[n],(node*)((char*)p+257*exp2i(n)));
        }
        return p;
    }else{
        free_tab[n].first = p->next;
        return p;
    }
}

void* bmalloc(int n){
    n = getindex(n);
    char* p = (char*)getn(n);
    if(p==0) return 0;
    *p = n;
    return p+1;
}

void erase(int index, int size, int n){
    node* p = free_tab[n].first;
    int ibuddy = index^exp2i(n);
    node* block = (node*)(mem+ibuddy*257);
    node* prev = p;
    while(p!=0){
        if(p==block){
            if(ibuddy<index) index = ibuddy;
            if(n<imax) erase(index,size*2,n+1);
            if(p==prev) free_tab[n].first = p->next;
            else prev->next = p->next;
            return;
        }
        prev = p;
        p = p->next;
    }
    append(&free_tab[n],(node*)(mem+index*257));
}

void bdispose(void* p){
    int index,n,size;
    if(p==0) return;
    index = ((char*)p-mem-1)/257;
    n = *((char*)p-1);
    size = 257*exp2i(n);
    erase(index,size,n);
}

int main(){
    free_tab[imax].first = (node*)mem;
    char* s = bmalloc(10);
    bdispose(s);
}

