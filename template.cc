/*
************************************************
*快速幂, 乘法逆元
************************************************
*/

// 快速幂计算 x^y % mod, (x >= 0 && y >= 0)
long long quickmul(long long x, long long y, long long mod /*= LONG_LONG_MAX*/) {
    long long ret = 1, cur = x % mod;
    while(y) {
        if(y & 1) {
            ret = (ret * cur) % mod;
        }
        y >>= 1;
        if(y) {
            cur = (cur * cur) % mod;
        }
    }
    return ret;
};

long long inv(long long x, long long mod /*= LONG_LONG_MAX*/) {
    return quickmul(x, mod - 2, mod);
}

/*
************************************************
*dijkstra最短路算法
************************************************
*/

//@edges[i][j]  : 结点i到结点edges[i][j].first的距离为edges[i][j].second
//@n            : 结点数, 0 ~ (n - 1)
//@src          : 源结点
//@return value : 结点src到所有结点的距离, LONG_LONG_MAX表示不可达
//@complexity   : O(V + ElogE)
vector<long long> dijkstra(vector<vector<pair<int, long long>>> &edges, int n, int src) {
    vector<long long> dist(n, LONG_LONG_MAX);
    priority_queue<pair<long long, int>, vector<pair<long long, int>>, greater<pair<long long, int>>> pq;
    pq.push({0LL, src});
    while(!pq.empty()) {
        auto [d, index] = pq.top();
        pq.pop();
        if(d >= dist[index]) {
            continue;
        }
        dist[index] = d;
        for(auto [next, t] : edges[index]) {
            pq.push({dist[index] + t, next});
        }
    }
    return dist;
}

/*
************************************************
*bfs最短路算法, 无权值
************************************************
*/

//@edges[i][j]  : 结点i可达结点edges[i][j]
//@n            : 结点数, 0 ~ (n - 1)
//@src          : 源结点
//@return value : 结点src到所有结点的距离, INT_MAX表示不可达
vector<int> bfs(vector<vector<int>> &edges, int n, int src) {
    vector<int> dist(n, INT_MAX);
    dist[src] = 0;
    queue<int> q;
    q.push(src);
    while(!q.empty()) {
        int cur = q.front();
        q.pop();
        for(auto next : edges[cur]) {
            if(dist[next] > dist[cur] + 1) {
                dist[next] = dist[cur] + 1;
                q.push(next);
            }
        }
    }
    return dist;
}

/*
************************************************
* KMP字符串匹配算法
************************************************
*/

//@haystack : 被匹配字符串
//@needle   : 匹配字符串
int strStr(string haystack, string needle) {
    if(needle.empty()) {
        return 0;
    }
    int nn = needle.size(), nh = haystack.size();
    vector<int> next(nn, 0);
    for(int i = 1; i < nn; i++) {
        int index = next[i - 1];
        while(index > 0 && needle[i] != needle[index]) {
            index = next[index - 1];
        }
        next[i] = index + (needle[i] == needle[index]);
    }
    for(int i = 0, k = 0; i < nh; i++) {
        while(haystack[i] != needle[k] && k > 0) {
            k = next[k - 1];
        }
        if(haystack[i] == needle[k]) {
            k++;
        }
        if(k == nn) {
            return i - nn + 1;
        }
    }
    return -1;
}

/*
************************************************
* 线段树
************************************************
*/

class segmentTree {
private:
    int n_;
    std::vector<long long> d_;
    std::vector<long long> t_;
    long long mod_;

    void build_(int s, int e, int node, const std::vector<int> &nums) {
        if (s == e) {
            d_[node] = nums[s];
            return;
        }
        int left = node * 2 + 1, right = node * 2 + 2;
        int m = s + (e - s) / 2;
        build_(s, m, left, nums);
        build_(m + 1, e, right, nums);
        d_[node] = (d_[left] + d_[right]) % mod_;
    }

    void update_(int s, int e, int node, int index, int val) {
        if (s == e) {
            d_[node] = val;
            return;
        }
        int m = s + (e - s) / 2;
        int left = node * 2 + 1, right = node * 2 + 2;
        if (index <= m) {
            update_(s, m, left, index, val);
        } else {
            update_(m + 1, e, right, index, val);
        }
        d_[node] = (d_[left] + d_[right]) % mod_;
    }

    void add_(int s, int e, int node, int l, int r, int val) {
        if (l == s && r == e) {
            t_[node] = (t_[node] + val) % mod_;
            return;
        }
        d_[node] = (d_[node] + (long long)val * (r - l + 1)) % mod_;
        int m = s + (e - s) / 2;
        int left = node * 2 + 1, right = node * 2 + 2;
        if (r <= m) {
            add_(s, m, left, l, r, val);
        } else if (l > m) {
            add_(m + 1, e, right, l, r, val);
        } else {
            add_(s, m, left, l, m, val);
            add_(m + 1, e, right, m + 1, r, val);
        }
    }

    long long range_(int s, int e, int node, int l, int r) {
        if (l == s && r == e) {
            return (d_[node] + (e - s + 1) * t_[node]) % mod_;
        }
        int m = s + (e - s) / 2;
        int left = node * 2 + 1, right = node * 2 + 2;
        if (t_[node] != 0) {
            d_[node] = (d_[node] + (e - s + 1) * t_[node]) % mod_;
            t_[left] = (t_[left] + t_[node]) % mod_;
            t_[right] = (t_[right] + t_[node]) % mod_;
            t_[node] = 0;
        }
        if (r <= m) {
            return range_(s, m, left, l, r);
        } else if (l > m) {
            return range_(m + 1, e, right, l, r);
        } else {
            return (range_(s, m, left, l, m) + range_(m + 1, e, right, m + 1, r)) % mod_;
        }
    }
public:
    segmentTree(const std::vector<int> &nums, long long mod /*= LONG_LONG_MAX*/) : d_(4 * nums.size()), t_(4 * nums.size()) {
        n_ = nums.size();
        mod_ = mod;
        build_(0, n_ - 1, 0, nums);
    }
    
    void update(int index, int val) { // index -> val
        update_(0, n_ - 1, 0, index, val);
    }

    void add(int l, int r, int val) { // [l, r] -> val
        add_(0, n_ - 1, 0, l, r, val);
    }

    long long range(int l, int r) { // [l, r]
        return (range_(0, n_ - 1, 0, l, r) + mod_) % mod_;
    }
};

/*
************************************************
* 树状数组
************************************************
*/

class biTree {
private:
    vector<long long> tree_;

    int lowBit_(int x) {
        return x & -x;
    }
public:
    biTree(vector<int>& nums) : tree_(nums.size() + 1) {
        for (int i = 0; i < nums.size(); i++) {
            add(i, nums[i]);
        }
    }
    
    void add(int index, long long val) { // 更新 nums[index] = nums[index] + val
        index++;
        while (index < tree_.size()) {
            tree_[index] += val;
            index += lowBit_(index);
        }
    }

    long long prefixSum(int index) { // nums[0, index)
        long long sum = 0;
        while (index > 0) {
            sum += tree_[index];
            index -= lowBit_(index);
        }
        return sum;
    }
};

/*
************************************************
* Manacher 算法
************************************************
*/

