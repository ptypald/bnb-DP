var svg1_el = document.getElementById("svg1");
var road = svg1_el.getBoundingClientRect();
var roadw = road.width;
var roadh = road.height;

var conf = {
    el: "#app",
    data: {
        switchTheme: true,
        googleChartFull: false,
        switchEgoFollow: true,
        vehicleDisplacement: 20,
        chooseVehToPlot: -1,
        /* sidebar */
        drawer: null,
        uploader: {
            name: "" ,
            file: null ,
            data: Data
        },
        loading: false,
        items:[
            { title: 'FAQs' },
            { title: 'About' }
        ],
        logos:[
            {title: 'fa-linkedin', url: 'http://www.linkedin.com'},
            {title: 'DSSL', url: 'http://www.dssl.tuc.gr'},
            {title: 'TUC', url:"http://www.tuc.gr/"}
        ],
        vehColors:[
            {title: 'pink'},
            // {title: 'pink', img: href="media/images/PinkCar.svg"},
            // {title: 'green', img: href="media/images/GreenCar.svg"}, 
            // {title: 'blue', img: href="media/images/BlueCar.svg"}
        ],
        show: false,
        timeStep: 0,
        playState: false,
        simSpeed: 10,
        slideLabels: [
            '1x', '2x', '3x', '4x', '5x', '6x',
            '7x', '8x', '9x', '10x',
        ],
        ptr: null,
        sidebarItems: [
        ],
        dialog: false,
        /* google charts */
        googleChartPlotDialogIndex: null,
        googleChartPlotDialogRow: {},
        column: {
            item1:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'ux', }
            ],
            item2:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'uy', }
            ],
            item3:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'vx' },
                { 'type': 'number', 'label': 'vdx' }
            ],
            item4:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'ax' }
            ],
            item5:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'y' }
            ],
            item6:[{ 'type': 'number', 'label': 'k' },
                { 'type': 'number', 'label': 'x' }
            ]
        },
        options: {
            item1: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'ux', },
                height: 0.5*screen.height,
                curveType: 'none',
                backgroundColor: { fill: 'white', },
                is3D: true 
            },
            item2: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'uy', },
                height: 0.5*screen.height,
                curveType: 'none'
            },
            item3: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'vx', },
                height: 0.5*screen.height,
                curveType: 'none'
                //curveType: 'function'
            },
            item4: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'ax', },
                height: 0.5*screen.height,
                curveType: 'none'
            },
            item5: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'y', },
                height: 0.5*screen.height,
                curveType: 'none'
            },
            item6: {
                title: '',
                hAxis: { title: 'Time Steps', },
                vAxis: { title: 'x', },
                height: 0.5*screen.height,
                curveType: 'none'
            },
        },
    },
    computed: {
        activeFab () {
            switch (this.tabs) {
                case 'one': return { 'class': 'purple', icon: 'account_circle' }
                case 'two': return { 'class': 'red', icon: 'edit' }
                case 'three': return { 'class': 'green', icon: 'keyboard_arrow_up' }
                default: return {}
            }
        },
        
        rows() {
            if (this.uploader.data) {
                if (this.chooseVehToPlot == this.uploader.data.id) {
                    var r = {
                        item1: [],
                        item2: [],
                        item3: [],
                        item4: [],
                        item5: [],
                        item6: [],
                    };

                    for (k =0; k < this.uploader.data.k + 1; k++){
                        if (k < this.uploader.data.k + 1) {
                            r.item1.push([ k , this.uploader.data["ux("+k+")"] ]);
                            r.item2.push([ k , this.uploader.data["uy("+k+")"] ]);
                        }
                        r.item3.push([ k , this.uploader.data["vx("+k+")"], this.uploader.data["vd"] ]);
                        r.item4.push([ k , this.uploader.data["ax("+k+")"] ]);
                        r.item5.push([k, this.uploader.data["y(" + k + ")"]]);
                        r.item6.push([k, this.uploader.data["x(" + k + ")"]]);
                    }
                }
                else{
                    var r = {
                        item1: [],
                        item2: [],
                        item3: [],
                    };

                    for (var i = 0; i < this.uploader.data.n; i++){
                        if (this.chooseVehToPlot == this.uploader.data["obst_id("+(i)+")"]){
                            for (k =0; k < this.uploader.data.k; k++){
                                //r.item1.push([ k , this.uploader.data['obst_x('+i+','+k+')'] ]);
                                r.item2.push([ k , this.uploader.data['obst_y('+i+','+k+')'] ]);
                                r.item3.push([ k , this.uploader.data['obst_v('+i+','+k+')'], this.uploader.data['obst_vd('+i+')']]);
                            }
                        }
                    }
                }
            }
            return r;
        },
        

        mToPX(){ return roadw/this.lanewidth; },
        carh() { return this.mToPX * 2.0; },
        carw() { return this.mToPX * this.uploader.data.C; },

        lanewidth(){
            var temp = 1e10, temp2 = -1;
            var max_x;
            var KMAX = this.uploader.data.k - 1;

            for (i=0; i < this.uploader.data.n; i++) {
                if (this.uploader.data["obst_x("+i+","+0+")"] < temp){
                    temp = this.uploader.data["obst_x("+i+","+0+")"] - 10;
                }
                max_x = Math.max(this.uploader.data["obst_x("+i+","+0+")"],   this.uploader.data["x("+0+")"]);
                if (max_x > temp2){
                    temp2 = max_x + 10;
                }
            }
            temp2 += 200;
            temp =  Math.min(temp, this.uploader.data["x("+0+")"]);
            
            return (temp2 - temp) / 2;
        },
    
        ego_x() {
            var x = {};
            for (k = 0; k < this.uploader.data.k; k++) {
                x[k] = (this.uploader.data['x('+k+')']) * this.mToPX;
                // x[k] = (this.uploader.data['x('+k+')'] - this.minxpos) * this.mToPX;
            }

            return x;
        },

        ego_y() {
            var y = {};
            for (k = 0; k < this.uploader.data.k; k++)
                y[k] = ( this.mToPX * ((this.uploader.data['y('+k+')']) * 3.3 + (3.3/2)) );

            return y;
        },

        obs_x() {
            var x = {};
            console.log(`${this.uploader.data.n}`);
            for (var i = 0; i < this.uploader.data.n; i++){
                x[i] = [];
                for (var k = 0; k < this.uploader.data.k; k++){
                    x[i][k] = (this.uploader.data['obst_x('+i+','+k+')']) * this.mToPX;
                    // x[i][k] = (this.uploader.data['obst_x('+i+','+k+')'] - this.minxpos) * this.mToPX;
                }
            }

            return x;
        },

        obs_y() {
            var y = {};
            for (i = 0; i < this.uploader.data.n; i++){
                y[i] = {};
                for (k = 0; k < this.uploader.data.k; k++)
                    y[i][k] = ( this.mToPX * ((this.uploader.data['obst_y('+i+','+k+')']) * 3.3 + (3.3/2)) );
            }
            return y;
        },

        followEgo() {
            if (this.switchEgoFollow) {
                console.log(`${this.ego_x[this.timeStep]}`);
                return -this.ego_x[this.timeStep] + roadw/2;
            }
            else
                return 0;
        },
    },

    methods: {
        fileChanged(file) {
            this.uploader.file = file;
            this.uploader.name = file.name;
            var reader = new FileReader();
            
            reader.onload = (e) => {
                var text = e.target.result;
                try {
                    eval(text);
                    this.uploader.data = Data;
                 } catch(err) {
                    console.log(`error reading file: ${err}`);
                }
            };

            reader.readAsText(file);

        },
        startSimulation(stopTime) {
            if (this.playState)
                return this.stopSimulation();

            this.playState = true;
            this.ptr = setInterval(() => {
                this.timeStep += 1;
                if (this.timeStep > stopTime - 1){
                    this.timeStep = 0;
                    return this.stopSimulation();
                }  
            }, (1000/this.simSpeed));
        },
        stopSimulation(){
            clearInterval(this.ptr);
            this.playState = false;
        },
        obsColoredText(obs) {
            var color;
            var k = this.timeStep;
            var v = this.uploader.data['obst_v('+obs+','+k+')'];
            var colors = [
                "rgb(255, 0, 0)",
                "rgb(255, 64, 0)",
                "rgb(255, 128, 0)",
                "rgb(255, 191, 0)",
                "rgb(255, 255, 0)",
                "rgb(191, 255, 0)",
                "rgb(128, 255, 0)",
                "rgb(64, 255, 0)"
            ];
            var step = (this.uploader.data['obst_vd('+obs+')'] / 8)
            for (var i = 0; i < 8; i++) {
                if ( (v >= (i)*step) && (v <= (1+i)*step) )
                    color = colors[i]
            }
            return color;
        },
        egoColoredText() {
            var color;
            var k = this.timeStep;
            var v = this.uploader.data['vx('+k+')'];
            var colors = [
                "rgb(255, 0, 0)",
                "rgb(255, 64, 0)",
                "rgb(255, 128, 0)",
                "rgb(255, 191, 0)",
                "rgb(255, 255, 0)",
                "rgb(191, 255, 0)",
                "rgb(128, 255, 0)",
                "rgb(64, 255, 0)"
            ];
            var step = (this.uploader.data.vd / 8)
            for (var i = 0; i < 8; i++) {
                if ( (v >= (i)*step) && (v <= (1+i)*step) )
                    color = colors[i]
            }
            return color;
        },
    },
};

Vue.use(VuetifyUploadButton);
Vue.use(VueCharts);
new Vue(window.conf);
Vue.use(Vuetify);

