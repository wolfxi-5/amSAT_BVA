#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include  <sstream>

using namespace std;

int main() {
    ifstream in("./result.txt");

    int size;
    in >> size;
    vector<int> result(size+1);
    for (int i = 1; i < size+1; i++) {
        in >> result[i];
    }
    in.close();

    // for (int i = 1; i < size+1; i++) {
    //     cout << result[i] << " ";
    // }

    ifstream out("./file1.cnf");
    string line;
    while (getline(out, line)) {
        if (line[0] == 'c' || line[0] == 'p') {
            continue;
        }

        istringstream iss(line);
        vector<int> numbers;
        int num;
        while (iss >> num) {
            if (num == 0) break;
            numbers.push_back(num);
        }

        bool flag = false;
        for (int i = 0; i < numbers.size(); i++) {
            if (numbers[i] == result[abs(numbers[i])]) {
                flag = true;
                break;
            }
        }
        if (!flag) cout << "unsat" << endl;
    }
    cout << "sat" << endl;
}