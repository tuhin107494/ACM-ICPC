/**    Tuhin ahmed                    **
*      Email:tuhin107494@gmail.com     *
*      university:comilla university  **
*/
#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
using namespace std;

#include<ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;
typedef tree< pair<int,pair<int,int> > ,null_type,less< pair<int,pair<int,int> > >,rb_tree_tag,
        tree_order_statistics_node_update>ordered_set;
#define TT ios::sync_with_stdio(false); cin.tie(0);cout.tie(0)
#define       ll                   long long int
#define       ull                  unsigned long long int
#define       vi                   vector<int>
#define       vc                   vector<char>
#define       vs                   vector<string>
#define       vll                  vector<long long int>
#define       vp                   vector<  pair<int,int> >
#define       pb                   push_back
#define       pob                  pop_back
#define       pll                  pair<long long  int, long long int>
#define       F                    first
#define       S                    second
#define       sc(x)                scanf("%lld",&x)
#define       sci(x)                scanf("%d",&x)
#define       sc2(x,y)             scanf("%lld %lld",&x,&y)
#define       pf                   printf
#define       min3(a,b,c)          min(a,b<c?b:c)
#define       max3(a,b,c)          max(a,b>c?b:c)
#define       all(v)               v.begin(), v.end()
#define       rall(v)               v.rbegin(), v.rend()
///============ CONSTANT ===============///
#define mx18  1000000000000000000
#define mx9   1000000007
#define mx8   100000007
#define mx7   10000006
#define mx6   1000056
#define mx5   200005
#define mx4   10005
#define inf   1<<30
#define eps   1e-9
#define mod   mx9
ll dx[]= {1,0,-1,0};
ll dy[]= {0,1,0,-1};
long double PI = acosl(-1);
///=============== Debugging ============================///
#ifndef ONLINE_JUDGE
#define       debug(x) cout << #x << " = " << x << endl
#define       debug2(x, y)             cout << #x << ": " << x << "  " << #y << ": " << y << endl;
#define       debug3(x, y, z)          cout << #x << ": " << x << "  " << #y << ": " << y << "  " << #z << ": " << z << endl;
#define       debug4(a, b, c, d)       cout << #a << ": " << a << "  " << #b << ": " << b << "  " << #c << ": " << c << "  " << #d << ": " << d << endl;
#endif
///=====================Bitmask===================///
//ordered_set st/;
//int Set(int N,it pos){return N=N  (1<<pos);}
//int reset(int N,int pos){return N= N & ~(1<<pos);}
//bool check(int N,int pos){return (bool)(N & (1<<pos));}
///========================================FUNCTION=========================================///
//bool check(int n){if(n==1) return false; for(int i=2; i*i<=n; i++){if(n%i==0) return false;} return true;}
//ll fact(ll n){if(n==0 or n==1)return 1; else return ((n%mod)*fact(n-1)%mod)mod;}
//ll big_mod(ll b,ll p,ll m ){ll res=1;while(p!=0){if(p&1)res=(res*b)%m;b=(b*b)%m;p=p>>1;}res=(res)%m;return res;}
//void seive(){for(ll i=2; i<mx6; i++){if(visit[i])continue;dv[i]=i;for(ll j=i*i; j<mx6; j+=i){dv[j]=i;visit[j]=true;}}}
//void build(int u,int b,int e){if(b==e){tr[u]=dif[b];return;}ll mid=(b+e)/2;build(2*u,b,mid);build(2*u+1,mid+1,e);tr[u]=gcd(tr[(2*u)],tr[(2*u)+1]);}
//ll quary(int u,int b,int e,int i,int j){if(e<i or b>j)return 0;else if(b>=i and e<=j){return tr[u];}int   mid=(b+e)/2;ll  left=quary(2*u,b,mid,i,j);ll right=quary((2*u)+1,mid+1,e,i,j);return  gcd(left,right);}
//void  update (int u,int b,int e,int i,int j,int x){if(e<i or b>j)return;else if(b>=i and e<=j){tr[u]=x;return;}int mid=(b+e)/2;update(2*u,b,mid,i,j,x);update((2*u)+1,mid+1,e,i,j,x);tr[u]=max(tr[2*u],tr[2*u +1]);}

//vector<ll> kmp_prefix_fun(string s){ll n=s.size();vector<ll>pi(n);for(ll i=1; i<n; i++){ll j=pi[i-1];while(j>0 and s[i]!=s[j])j=pi[j-1];if(s[i]==s[j])++j;pi[i]=j;}return pi;}
//void trie_add_string(string s){int cur=1;cnt[cur]++;for(int i=0; i<s.size(); i++){int  ch=s[i]-'a';if(!to[cur][ch])to[cur][ch]=++to_node;cur=to[cur][ch];cnt[cur]++;}track[cur]++;}
//int trie_quary(string s){int cur=1;for(int i=0; i<s.size(); i++){int ch=s[i]-'a';if(!to[cur][ch])return cnt[cur];cur=to[cur][ch];}return cnt[cur];}
//void sparse_table(){for(int i=1;i<=n;i++)table[i][0]=a[i];for(int k=1;k<20;k++){for(int i=1;i+(1<<k)-1<=n;i++){table[i][k]=min(table[i][k-1],table[i+(1<<(k-1))][k-1]);}}}36.5\   123456
//int sparse_quary(int l,int r){int len=r-l+1;int k=log2(len);return min(table[l][k],table[r-(1<<k)+1][k]);}
///====================================StartHere=================////////////

vector<ll>par,sz;
vector< pair<ll,pll> >v;
ll dv[mx6],cs=0;
bitset<mx6>visited;
void seive()
{
    for(ll i=2; i<mx6; i++)
        {
            if(visited[i])continue;
            dv[i]=i;
            for(ll j=i*i; j<mx6; j+=i)
                {
                    dv[j]=i;
                    visited[j]=true;
                }
            }
}

 void DSU(int _n){
      ll  n=_n;
        par.resize(n+1);
        sz.resize(n+1);
        for(int i=1; i<=n; i++)par[i]=i,sz[i]=1;
    }
    int Find(int a){
        if(a==par[a])return par[a];
        return par[a] = Find(par[a]);
    }
    void Union(int a, int b){
        a = Find(a);b = Find(b);
        if(a==b)return;
        if(sz[a] >= sz[b]){
            sz[a] += sz[b];
            par[b] = a;
        }
        else{
            par[a]=b;
            sz[b]+=sz[a];
        }
    }

void input()
{
   ll n,m,ans=0;
    cin>>n;
    
     vector<ll>v;
     for(int i=1;i<=n;i++)
     {
        ll l;
        cin>>l;
        if(l!=1)v.pb(l);
        else ans++;
     }

      DSU(mx6);
      set<ll>st;
      for(int i=0;i<v.size();i++)
      {
        vector<ll>vec;
        n=v[i]; 
        while(n!=1)
        {
            ll d=dv[n];
            while(n%d==0)n/=d;
            vec.pb(d);
            st.insert(d);
        }

        for(int j=0;j<vec.size();j++)
        {
       
        for(int k=j+1;k<vec.size();k++)
        {

            ll a=Find(vec[j]);
            ll b=Find(vec[k]);

        if(a==b)continue;
        Union(a,b);
        }
       }
     }

     for(auto it:st)
     {
        if(Find(it)==it)
        {
            ans++;
        }
     }

     cout<<"Case "<<++cs<<": "<<ans<<"\n";

}
void ifdef()
{
    #ifndef ONLINE_JUDGE
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    freopen("Error.txt", "w", stderr);
    #endif 
}
int main()
{
   TT;
   seive();
   //ifdef();
  
   int t=1;
    cin>>t;
    while(t--)
    {

        input();

    }
    return 0;
}
