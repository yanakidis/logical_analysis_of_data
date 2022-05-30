#include <iostream>
#include <vector>
#include <utility>
#include <set>
#include <cmath>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <string>

using namespace std;

// оператор вывода для строк
set <int> derOpR(vector <vector <int> > &matrix, vector <int> &rows) {
    set <int> columns;
    for (int j=0; j < matrix[0].size(); j++) {
        bool flag = true;
        for (int i=0; i < rows.size(); i++)
            if (matrix[rows[i]][j] != 1) {
                flag = false;
                break;
            }
        if (flag)
            columns.insert(j);
    }
    return columns;
}


// оператор вывода для столбцов
set <int> derOpC(vector <vector <int> > &matrix, set <int> &columns) {
    set <int> rows;
    for (int i=0; i < matrix.size(); i++) {
        bool flag = true;
        for (auto it = columns.begin(); it != columns.end(); it++)
            if (matrix[i][*it] != 1) {
                flag = false;
                break;
            }
        if (flag)
            rows.insert(i);
    }
    return rows;
}

// бинарный вектор в десятичное число
int bin_to_dec(vector <int> &vec) {
    int res = 0;
    unsigned long size = vec.size();
    for (int i=0; i < size; i++)
        res += vec[i]*pow(2, size - i - 1);
    return res;
}

// сравнение бинарных векторов
bool less_vec(vector <int> &a, vector <int> &b) {
    auto x = bin_to_dec(a);
    auto y = bin_to_dec(b);
    return (x < y);
}

// вспомогательная функция для сортировки (чтобы сортировка была по убыванию)
bool sort_descending(const pair<int,int> &a, const pair<int,int> &b) {
    return (a.first > b.first);
}

// сортировка строк матриц по убыванию
vector <vector <int> > sort_matrix_descending (vector <vector <int> > &matrix) {
    vector <pair<int, int> > b;
    for (int i=0; i < matrix.size(); i++)
        b.push_back(make_pair(bin_to_dec(matrix[i]), i));
    sort(b.begin(), b.end(), sort_descending);
    vector <vector <int> > new_matrix (matrix.size(), vector<int>(matrix[0].size(), 0));
    for (int i=0; i < b.size(); i++)
        new_matrix[i] = matrix[b[i].second];
    return new_matrix;
}


// транспонирование матрицы
vector <vector <int> > transpose(vector <vector <int> > &matrix) {
    vector <vector <int> > result(matrix[0].size(), vector <int> (matrix.size()));
    for (int i=0; i<matrix[0].size(); i++)
        for (int j=0; j<matrix.size(); j++)
            result[i][j] = matrix[j][i];
    return result;
}

// process
void process (set <int> &A, vector <int> &g, set <int> &C, set <int> &D,
              vector <vector <int> > &matrix, set <pair <set <int>, set <int> > > &concept_set) {
    bool flag = true;
    set <int> diff;
    set_difference(C.begin(), C.end(), A.begin(), A.end(), inserter(diff, diff.end()));
    if (not diff.empty())
        for (auto it=diff.begin(); it!= diff.end(); it++)
            if (less_vec(matrix[*it], g)) {
                flag = false;
                break;
            }
    if (flag) {
        concept_set.insert(make_pair(C, D));
    } else
        return;
    set <int> additional_set;
    for (int i=0; i < matrix.size(); i++)
        if (less_vec(g, matrix[i]))
            additional_set.insert(i);
    for (auto it=additional_set.begin(); it != additional_set.end(); it++) {
        C.insert(*it); // это и есть Z
        vector<int> f (1, *it);
        auto cols = derOpR(matrix, f);
        set <int> Y;
        set_intersection(D.begin(), D.end(), cols.begin(), cols.end(), inserter(Y, Y.end()));
        auto X = derOpC(matrix, Y);
        process(C, matrix[*it], X, Y, matrix, concept_set);
    }
}


// close by one
set <pair <set<int>, set<int> > > cbo (vector <vector <int> > &matrix) {
    set <pair <set <int>, set <int> > > concept_set;
    for (int i=0; i < matrix.size(); i++) {
        cout << i << "/" << matrix.size() << endl;
        set <int> A;
        A.insert(i);
        auto g = matrix[i];
        vector <int> rows (1, i);
        auto D = derOpR(matrix, rows);
        auto C = derOpC(matrix, D);
        process(A, g, C, D, matrix, concept_set);
    }
    vector <int> rows;
    auto A = derOpR(matrix, rows);
    auto B = derOpC(matrix, A);
    concept_set.insert(make_pair(B, A));
    return concept_set;
}

// функция для генерации гипотез
// генерирует все положительные или отрицательные гипотезы для заданного контекста
// если positive == true, то генерирует положительные гипотезы, иначе отрицательные
// если optim == true, то транспонируем
set <set <int> > hypothesesMaker(vector <vector <int> > &matrix, vector <int> &target, bool positive,
                                 bool optim) {
    vector <vector <int> > X;
    vector <vector <int> > Y;
    
    // выделим нужные подматрицы с нужным таргетом
    // X - для нахождения понятий
    // Y - для перебора противоположных объектов
    
    if (positive)
        for (int i=0; i<target.size(); i++) {
            if (target[i] == 1)
                X.push_back(matrix[i]);
            else
                Y.push_back(matrix[i]);
        }
    else
        for (int i=0; i<target.size(); i++) {
            if (target[i] == 0)
                X.push_back(matrix[i]);
            else
                Y.push_back(matrix[i]);
        }
    
    // для начала найдём все формальные понятия положительного/отрицательного контекста
    // затем выберем из них те, которые удовлеторяют определению гипотезы
    set <pair <set<int>, set<int> > > concepts;
    cout << "starting cbo" << endl;
    
    if (not optim)
        concepts = cbo(X);
    else {
        auto X_new = transpose(X);
        auto new_concepts = cbo(X_new);
        for (auto it=new_concepts.begin(); it!=new_concepts.end(); it++){
            concepts.insert(make_pair((*it).second, (*it).first));
        }
    }
    
    set <set <int> > hypotheses;
    bool flag;
    vector <set <int> > der_Y;
    
    for (int i=0; i <Y.size(); i++) {
        vector <int> g (1, i);
        auto der_g = derOpR(Y, g);
        der_Y.push_back(der_g);
    }

    for (auto it=concepts.begin(); it != concepts.end(); it++){
        flag = true;
        for (auto der_g=der_Y.begin(); der_g != der_Y.end(); der_g++) {
            if (includes((*der_g).begin(), (*der_g).end(),
                         (*it).second.begin(), (*it).second.end())) {
                flag = false;
                break;
            }
        }
        if (flag)
            hypotheses.insert((*it).second);
    }
    return hypotheses;
}

// дсм-метод, возвращающий y_pred (y_pred_golos)
pair <vector <int>, vector <int> > jsm (vector <vector <int> > &X_train, vector <vector <int> > &X_test, vector <int> &y_train,
                  bool optim) {
    
    cout << "pos_hyp" << endl;
    auto pos_hyp = hypothesesMaker(X_train, y_train, true, optim);
    cout << "neg_hyp" << endl;
    auto neg_hyp = hypothesesMaker(X_train, y_train, false, optim);
    
    vector <int> y_pred (X_test.size(), 0);
    vector <int> y_pred_golos (X_test.size(), 0);
    
    vector <set <int> > der_X_test;
    for (int i=0; i <X_test.size(); i++) {
        vector <int> g (1, i);
        auto der_g = derOpR(X_test, g);
        der_X_test.push_back(der_g);
    }
    
    int i = 0;
    cout << "i :" << endl;
    
    chrono::steady_clock::time_point begin = chrono::steady_clock::now();
    // классический подход
    
    bool flag_pos;
    bool flag_neg;

    for (auto der_g=der_X_test.begin(); der_g != der_X_test.end(); der_g++) {
        flag_pos = false;
        flag_neg = false;
        for (auto it=pos_hyp.begin(); it != pos_hyp.end(); it++)
            if (includes((*der_g).begin(), (*der_g).end(),
                         (*it).begin(), (*it).end())) {
                flag_pos = true;
                break;
            }
        for (auto it=neg_hyp.begin(); it != neg_hyp.end(); it++)
            if (includes((*der_g).begin(), (*der_g).end(),
                         (*it).begin(), (*it).end())) {
                flag_neg = true;
                break;
            }
        cout << i << "/" << X_test.size() << endl;
        cout << "flag_neg = " << flag_neg << endl;
        cout << "flag_pos = " << flag_pos << endl;
        if (flag_neg and flag_pos)
            y_pred[i] = -1; // противоречивая классификация
        else if (flag_pos)
            y_pred[i] = 1; // положительный класс
        else if (flag_neg)
            y_pred[i] = 0; // отрицательный класс
        else
            y_pred[i] = -2; // неопределенная классификация
        i++;
    }
    chrono::steady_clock::time_point end = chrono::steady_clock::now();
    cout << "classic = "<< chrono::duration_cast<chrono::microseconds>(end - begin).count() << endl;
    
    i = 0;
    cout << "i :" << endl;
    
    begin = chrono::steady_clock::now();
    // голосование
    
    int count_pos;
    int count_neg;
    
    for (auto der_g=der_X_test.begin(); der_g != der_X_test.end(); der_g++) {
        count_pos = 0;
        count_neg = 0;
        for (auto it=pos_hyp.begin(); it != pos_hyp.end(); it++)
            if (includes((*der_g).begin(), (*der_g).end(),
                         (*it).begin(), (*it).end())) {
                count_pos++;
            }
        for (auto it=neg_hyp.begin(); it != neg_hyp.end(); it++)
            if (includes((*der_g).begin(), (*der_g).end(),
                         (*it).begin(), (*it).end())) {
                count_neg++;
            }
        cout << i << "/" << X_test.size() << endl;
        cout << "count_pos = " << count_pos << endl;
        cout << "count_neg = " << count_neg << endl;
        if (count_pos == count_neg)
            y_pred_golos[i] = -1; // противоречивая классификация
        else if (count_pos > count_neg)
            y_pred_golos[i] = 1; // положительный класс
        else
            y_pred_golos[i] = 0; // отрицательный класс
        i++;
    }
    end = chrono::steady_clock::now();
    cout << "golos = "<< chrono::duration_cast<chrono::microseconds>(end - begin).count() << endl;
    
    return make_pair(y_pred, y_pred_golos);
}

int main(int argc, const char * argv[]) {
}
