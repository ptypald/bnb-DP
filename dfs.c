// C program for different tree traversals 
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include <float.h>
#include <time.h>
  
#define STEPS 25

double best = DBL_MAX;
double x_path[STEPS + 1], y_path[STEPS + 1], v_path[STEPS + 1], ux_path[STEPS + 1];
double x_opt[STEPS + 1], y_opt[STEPS + 1], v_opt[STEPS + 1], ux_opt[STEPS + 1];
double root_best = DBL_MAX;

struct {
	double vd, T, C, safety;
	double x0, y0, v0, a0;
	double *obst_x, *obst_y, *obst_v;
	int obst_x_len, obst_y_len, obst_v_len;
	int numlanes, numsteps, n;
	int *skip, nskip;

	int trim;
}P = { 0 };

/* obstacle solution */
struct {
	double **obst_x;
	double **obst_y;
	double **obst_v;
}S = { 0 };

struct node { 
    int stage, infeasible;
    int laneChnageCount;
    double x, y, v, ux, cost;

    struct node* leftUp; 
    struct node* leftDown; 
    struct node* leftSame; 
    
    struct node* middleUp;
    struct node*  middleDown;
    struct node*  middleSame;
    
    struct node* rightUp; 
    struct node* rightDown;
    struct node* rightSame; 
}; 

struct node* newNode(int stage, double cost, int infeasible) { 
    struct node* node = (struct node*) 
        malloc(sizeof(struct node)); 

    node->stage = stage;
    node->cost = cost;
    node->leftUp = node->leftDown = node->leftSame = NULL; 
    node->middleUp = node->middleDown = node->middleSame = NULL;
    node->rightUp = node->rightDown = node->rightSame = NULL; 
     
    node->infeasible = 0;
    node->laneChnageCount = -1;

    return (node); 
} 

void read_P(void) {

	assert((P.obst_x = (double*)calloc(sizeof(double*), 50)));
	assert((P.obst_y = (double*)calloc(sizeof(double*), 50)));
	assert((P.obst_v = (double*)calloc(sizeof(double*), 50)));	
	
	char buf[1024];
	double dval;
	int ival;
	while (fgets(buf, sizeof(buf), stdin))
	{
        fprintf(stderr, "%s",buf);
		if (buf[0] == '\n')
			break;
		if (sscanf(buf, "\"vd\":%lf", &dval) == 1)
			P.vd = dval;
		if (sscanf(buf, "\"numlanes\":%d", &ival) == 1)
			P.numlanes = ival;
		if (sscanf(buf, "\"numsteps\":%d", &ival) == 1)
			P.numsteps = ival;
		if (sscanf(buf, "\"safety\":%lf\n", &dval) == 1)
			P.safety = dval;
		if (sscanf(buf, "\"C\":%lf", &dval) == 1)
			P.C = dval;
		if (sscanf(buf, "\"T\":%lf", &dval) == 1)
			P.T = dval;
		if (sscanf(buf, "\"x(0)\":%lf", &dval) == 1)
			P.x0 = dval;
		if (sscanf(buf, "\"y(0)\":%lf", &dval) == 1)
			P.y0 = dval;
		if (sscanf(buf, "\"v(0)\":%lf", &dval) == 1)
			P.v0 = dval;
		if (sscanf(buf, "\"a(0)\":%lf\n", &dval) == 1)
			P.a0 = dval;
		if (sscanf(buf, "\"obst_x(%d,0)\":%lf", &ival, &dval) == 2) {
			P.obst_x[ival] = dval;
            P.obst_x_len = fmax(P.obst_x_len, ival + 1);
		}
		if (sscanf(buf, "\"obst_y(%d,0)\":%lf", &ival, &dval) == 2) {
			P.obst_y[ival] = dval;
		}
		if (sscanf(buf, "\"obst_v(%d,0)\":%lf", &ival, &dval) == 2) {
			P.obst_v[ival] = dval;
		}		
 		memset(buf, 0, sizeof(buf));
 	} 

	P.n = P.obst_x_len;
}

void init_S(int numsteps, double T, int n, double *obst_x, double *obst_y, double *obst_v) {
	int i, k;
    
	/* allocate */
	assert((S.obst_x = (double**)calloc(sizeof(double*), numsteps + 1)));
	assert((S.obst_y = (double**)calloc(sizeof(double*), numsteps + 1)));
	assert((S.obst_v = (double**)calloc(sizeof(double*), numsteps + 1)));
	for (k = 0; k < numsteps + 1; k++) {
		assert((S.obst_x[k] = (double*)calloc(sizeof(double), n)));
		assert((S.obst_y[k] = (double*)calloc(sizeof(double), n)));
		assert((S.obst_v[k] = (double*)calloc(sizeof(double), n)));
	}

    for (int o = 0; o < n; o++) {
        S.obst_x[0][o] = obst_x[o];
        S.obst_y[0][o] = obst_y[o];
        S.obst_v[0][o] = obst_v[o];
    }
	/* compute */
	for (k = 0; k < numsteps; k++) {
		for (i = 0; i < n; i++) {
			S.obst_x[k+1][i] = S.obst_x[k][i] + S.obst_v[k][i] * T;
			S.obst_y[k+1][i] = S.obst_y[k][i];
			S.obst_v[k+1][i] = S.obst_v[k][i];
		}
	}
}

double crash(struct node* node) {
	int i; 
	double dx;
	double sgap;
	double cost = 0; 
	double L = 5.0;

    int k = node->stage;
    double y = node->y;
 	for (i = 0; i < P.n; i++) {
        // fprintf(stderr, "(%d) %f -- %f \n", i, S.obst_y[k][i], y);
	    if (S.obst_y[k][i] != y) {
			continue;
        }

		dx = fabs(S.obst_x[k][i] - node->x);

		if (S.obst_x[k][i] - node->x >= 0)
            sgap = P.safety * node->v + L;
		else
            sgap = P.safety * S.obst_v[k][i] + L;
			
		if (dx < sgap ){
			cost += 1.0;
            node->infeasible = 1;
            // fprintf(stderr, "infeasible at %f with obst %d\n", node->x, i);
        }
	}
	return cost;
}

int temp_data = 0, count = 0;
void printPreorder(struct node* nodes) { 
    // path[0] = nodes->ux;
    if ((nodes == NULL) || nodes->infeasible == 1)
        return; 
    
    x_path[nodes->stage - 1] = nodes->x;
    y_path[nodes->stage - 1] = nodes->y;
    v_path[nodes->stage - 1] = nodes->v;
    ux_path[nodes->stage - 1] = nodes->ux;

    if (nodes->stage == P.numsteps && nodes->cost < best) {
        best = nodes->cost;
        for (int i = 0; i <= P.numsteps; i++) {
            x_opt[i] = x_path[i];
            y_opt[i] = y_path[i];
            v_opt[i] = v_path[i];
            ux_opt[i] = ux_path[i];
        }
    }
    
    printPreorder(nodes->leftUp);
    printPreorder(nodes->leftDown);
    printPreorder(nodes->leftSame);

    printPreorder(nodes->middleUp);
    printPreorder(nodes->middleDown);
    printPreorder(nodes->middleSame);

    printPreorder(nodes->rightUp);
    printPreorder(nodes->rightDown);
    printPreorder(nodes->rightSame); 
} 

int countTest = 0;
void dfs(struct node* root) {
    // fprintf(stderr, "stage: %d \n", root->stage);
    
    if (root->stage > P.numsteps || root->infeasible == 1)
        return;
    
    int stage = root->stage += 1;
    if (root->stage == P.numsteps && root->cost < root_best) {
        root_best = root->cost;
        // printf("root_best: %f \n", root_best);
    }
    else if (root->cost >= root_best)
        return;
    
    fprintf(stderr, "processed: %d \n", ++countTest);
    // int stage = root->stage += 1; // TODO: check this
    int dy, dux;
    double u = 2;
    
    /* leftUp node assuming ux = -u -- uy = +1 */
    dy = 1.0;
    root->leftUp = newNode(stage, 0, 0);
    root->leftUp->ux = -u;
    root->leftUp->y = root->y + dy;   //TODO
    if (root->leftUp->y != root->y)
        root->leftUp->laneChnageCount = root->laneChnageCount + 1;
    root->leftUp->x = root->x + root->v + 0.5*root->leftUp->ux*P.T;
    root->leftUp->v = root->v + (-u)*P.T;
    root->leftUp->cost += 0.5 * pow(root->leftUp->ux, 2) + pow(dy, 2) + 0.5 * pow(root->leftUp->v - P.vd, 2) + root->cost;// + crash(here, 0);
    crash(root->leftUp);

    /* leftUp node assuming ux = -u -- uy = -1 */
    dy = -1.0;
    root->leftDown = newNode(stage, 0, 0);
    root->leftDown->ux = -u;
    root->leftDown->y = root->y + dy;   //TODO
    if (root->leftDown->y != root->y)
        root->leftDown->laneChnageCount = root->laneChnageCount + 1;
    root->leftDown->x = root->x + root->v + 0.5*root->leftDown->ux*P.T;
    root->leftDown->v = root->v + (-u)*P.T;
    root->leftDown->cost += 0.5 * pow(root->leftDown->ux, 2) + pow(dy, 2) + 0.5 * pow(root->leftDown->v - P.vd, 2) + root->cost;// + crash(here, 0);
    crash(root->leftDown);

    /* leftUp node assuming ux = -u -- uy = 0 */
    dy = 0.0;
    root->leftSame = newNode(stage, 0, 0);
    root->leftSame->ux = -u;
    root->leftSame->y = root->y + dy;   //TODO
    if (root->leftSame->y != root->y)
        root->leftSame->laneChnageCount = root->laneChnageCount + 1;
    root->leftSame->x = root->x + root->v + 0.5*root->leftSame->ux*P.T;
    root->leftSame->v = root->v + (-u)*P.T;
    root->leftSame->cost += 0.5 * pow(root->leftSame->ux, 2) + pow(dy, 2) + 0.5 * pow(root->leftSame->v - P.vd, 2) + root->cost;// + crash(here, 0);
    crash(root->leftSame);

    /* middle node assuming ux = 0 -- uy = +1 */
    dy = 1.0;
    root->middleUp = newNode(stage, 0, 0);
    root->middleUp->ux = 0.0;
    root->middleUp->y = root->y + dy;   //TODO
    if (root->middleUp->y != root->y)
        root->middleUp->laneChnageCount = root->laneChnageCount + 1;
    root->middleUp->x = root->x + root->v + 0.5*root->middleUp->ux*P.T;
    root->middleUp->v = root->v + (0)*P.T;
    root->middleUp->cost = 0.5 * pow(root->middleUp->ux, 2) + pow(dy, 2) + 0.5 * pow(root->middleUp->v - P.vd, 2) + root->cost;
    crash(root->middleUp);

    /* middle node assuming ux = 0 -- uy = -1 */
    dy = -1.0;
    root->middleDown = newNode(stage, 0, 0);
    root->middleDown->ux = 0.0;
    root->middleDown->y = root->y + dy;   //TODO
    if (root->middleDown->y != root->y)
        root->middleDown->laneChnageCount = root->laneChnageCount + 1;
    root->middleDown->x = root->x + root->v + 0.5*root->middleDown->ux*P.T;
    root->middleDown->v = root->v + (0)*P.T;
    root->middleDown->cost = 0.5 * pow(root->middleDown->ux, 2) + pow(dy, 2) + 0.5 * pow(root->middleDown->v - P.vd, 2) + root->cost;
    crash(root->middleDown);

    /* middle node assuming ux = 0 -- uy = 0 */
    dy = 0.0;
    root->middleSame = newNode(stage, 0, 0);
    root->middleSame->ux = 0.0;
    root->middleSame->y = root->y + dy;   //TODO
    if (root->middleSame->y != root->y)
        root->middleSame->laneChnageCount = root->laneChnageCount + 1;
    root->middleSame->x = root->x + root->v + 0.5*root->middleSame->ux*P.T;
    root->middleSame->v = root->v + (0)*P.T;
    root->middleSame->cost = 0.5 * pow(root->middleSame->ux, 2) + pow(dy, 2) + 0.5 * pow(root->middleSame->v - P.vd, 2) + root->cost;
    crash(root->middleSame);

    /* right node assuming ux = u */
    dy = 1.0;
    root->rightUp = newNode(stage, 0, 0);
    root->rightUp->ux = u;
    root->rightUp->y = root->y + dy;   //TODO
    if (root->rightUp->y != root->y)
        root->rightUp->laneChnageCount = root->laneChnageCount + 1;
    root->rightUp->x = root->x + root->v + 0.5*root->rightUp->ux*P.T;
    root->rightUp->v = root->v + (u)*P.T;
    root->rightUp->cost += 0.5 * pow(root->rightUp->ux, 2) + pow(dy, 2) + 0.5 * pow(root->rightUp->v - P.vd, 2) + root->cost;
    crash(root->rightUp);

    /* right node assuming ux = u */
    dy = -1.0;
    root->rightDown = newNode(stage, 0, 0);
    root->rightDown->ux = u;
    root->rightDown->y = root->y + dy;   //TODO
    if (root->rightDown->y != root->y)
        root->rightDown->laneChnageCount = root->laneChnageCount + 1;
    root->rightDown->x = root->x + root->v + 0.5*root->rightDown->ux*P.T;
    root->rightDown->v = root->v + (u)*P.T;
    root->rightDown->cost += 0.5 * pow(root->rightDown->ux, 2) + pow(dy, 2) + 0.5 * pow(root->rightDown->v - P.vd, 2) + root->cost;
    crash(root->rightDown);

    /* right node assuming ux = u */
    dy = 0.0;
    root->rightSame = newNode(stage, 0, 0);
    root->rightSame->ux = u;
    root->rightSame->y = root->y + dy;   //TODO
    if (root->rightSame->y != root->y)
        root->rightSame->laneChnageCount = root->laneChnageCount + 1;
    root->rightSame->x = root->x + root->v + 0.5*root->rightSame->ux*P.T;
    root->rightSame->v = root->v + (u)*P.T;
    root->rightSame->cost += 0.5 * pow(root->rightSame->ux, 2) + pow(dy, 2) + 0.5 * pow(root->rightSame->v - P.vd, 2) + root->cost;
    crash(root->rightSame);

    /* check for negative speed */
    if (root->leftUp->v < 0 || root->leftUp->v > (P.vd) || root->leftUp->y < 0 || root->leftUp->y > P.numlanes - 1 || root->leftUp->laneChnageCount > 1) {
        root->leftUp->infeasible = 1;
    }
    if (root->leftDown->v < 0 || root->leftDown->v > (P.vd) || root->leftDown->y < 0 || root->leftDown->y > P.numlanes - 1 || root->leftDown->laneChnageCount > 1) {
        root->leftDown->infeasible = 1;
    }
    if (root->leftSame->v < 0 || root->leftSame->v > (P.vd) || root->leftSame->y < 0 || root->leftSame->y > P.numlanes - 1 || root->leftSame->laneChnageCount > 1) {
        root->leftSame->infeasible = 1;
    }

    if (root->middleUp->v < 0 || root->middleUp->v > (P.vd) || root->middleUp->y < 0 || root->middleUp->y > P.numlanes - 1 || root->middleUp->laneChnageCount > 1) {
        root->middleUp->infeasible = 1;
    }
    if (root->middleDown->v < 0 || root->middleDown->v > (P.vd) || root->middleDown->y < 0 || root->middleDown->y > P.numlanes - 1 || root->middleDown->laneChnageCount > 1) {
        root->middleDown->infeasible = 1;
    }
    if (root->middleSame->v < 0 || root->middleSame->v > (P.vd) || root->middleSame->y < 0 || root->middleSame->y > P.numlanes - 1 || root->middleSame->laneChnageCount > 1) {
        root->middleSame->infeasible = 1;
    }

    if (root->rightUp->v < 0 || root->rightUp->v > (P.vd) || root->rightUp->y < 0 || root->rightUp->y > P.numlanes - 1 || root->rightUp->laneChnageCount > 1) {
        root->rightUp->infeasible = 1;
    }
    if (root->rightDown->v < 0 || root->rightDown->v > (P.vd) || root->rightDown->y < 0 || root->rightDown->y > P.numlanes - 1 || root->rightDown->laneChnageCount > 1) {
        root->rightDown->infeasible = 1;
    }
    if (root->rightSame->v < 0 || root->rightSame->v > (P.vd) || root->rightSame->y < 0 || root->rightSame->y > P.numlanes - 1 || root->rightSame->laneChnageCount > 1) {
        root->rightSame->infeasible = 1;
    } 

    dfs(root->leftUp);
    dfs(root->leftDown);
    dfs(root->leftSame);

    dfs(root->middleUp);
    dfs(root->middleDown);
    dfs(root->middleSame);

    dfs(root->rightUp);
    dfs(root->rightDown);
    dfs(root->rightSame);
}

int main() { 

    clock_t start, end;
    double cpu_time_used;

    read_P();
    init_S(P.numsteps, P.T, P.n, P.obst_x, P.obst_y, P.obst_v);
    
    struct node* root = newNode(0, 0, 0);
    root->v = P.v0;
    root->y = P.y0;
    root->x = P.x0;
    root->ux = 0.0;
    root->stage = 0;
    root->cost = 0.5 * pow(P.v0 - P.vd, 2);

    start = clock();
    dfs(root);
    printPreorder(root); 
    
    printf("\n");
    end = clock();
    cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
    printf("CPU-time: %.4f \n", cpu_time_used);

    FILE *f = fopen("viz/data/data.js", "w+");
    fprintf(f, "var Data = { \n");
    for (int k = 0; k <= P.numsteps; k++) {
        // printf("(%d) %f -- %f -- %f -- %f -- %f \n", i, best_path[i], S.obst_x[i][0], S.obst_x[i][1], S.obst_x[i][2], S.obst_x[i][3]);
        fprintf(f, "\"x(%d)\":%.3f,\n", k, x_opt[k]);
        fprintf(f, "\"y(%d)\":%.3f,\n", k, y_opt[k]);
        fprintf(f, "\"vx(%d)\":%.3f,\n", k, v_opt[k]);
        fprintf(f, "\"vy(%d)\":%.3f,\n", k, 0.0);
        fprintf(f, "\"ux(%d)\":%.3f,\n", k, ux_opt[k]);
        fprintf(f, "\"uy(%d)\":%.3f,\n", k, 0.0);
        for (int i = 0; i < P.n; i++) {
            fprintf(f, "\"obst_x(%d,%d)\":%.3f,\n", i, k, S.obst_x[k][i]);
            fprintf(f, "\"obst_y(%d,%d)\":%.3f,\n", i, k, S.obst_y[k][i]);
            fprintf(f, "\"obst_v(%d,%d)\":%.3f,\n", i, k, S.obst_v[k][i]);
        }
    }
    fprintf(f, "\"n\":%d,\n", P.n);
    fprintf(f, "\"k\":%d,\n", P.numsteps);
    fprintf(f, "\"numlanes\":%d,\n", P.numlanes);
    fprintf(f, "\"vd\":%f,\n", P.vd);
    fprintf(f, "\"Step\":%f,\n", P.T);
    fprintf(f, "\"C\":%f, \n", P.C);
    fprintf(f, "\"safety\":%f, \n", P.safety);
    fprintf(f, "\"a(0)\":%f, \n", P.a0);
    fprintf(f, "};\n");
    fclose(f);
    
    return 0; 
} 