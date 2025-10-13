import { watch, build } from 'rolldown';
import { createServer } from 'http';
import { createReadStream, constants } from 'fs';
import { access } from 'fs/promises';
import * as path from 'path';

/**
 * @param {string[]} cmd
 */
async function run(cmd) {
    /** @type {import('rolldown').BuildOptions[]} */
    const opt = [{
        output: {
            sourcemap: true,
            file: 'dist/tests.js',
            format: 'iife',
        },
        input: {
            mainFiles: 'src/tests.ts',
        },
    }];
    switch (cmd[0]) {
        case 'serve': {
            const root = path.dirname(new URL(import.meta.url).pathname);
            /** @type {{[name: string]: string}} */
            const mimes = {
                'json': 'application/json',
                'js': 'application/javascript',
                'html': 'text/html',
                'css': 'text/css',
                'png': 'image/png',
                'ico': 'image/x-ico',
            };
            const server = createServer((request, response) => {
                let url = request.url;
                if (url === '/') {
                    url = '/index.html';
                }
                if (url) {
                    const filePath = path.join(root, url);
                    const ext = path.extname(filePath).slice(1);
                    const mime = mimes.hasOwnProperty(ext) ? mimes[ext] : 'application/octet-stream';
                    access(filePath, constants.R_OK).then(() => {
                        response.writeHead(200, {'Content-Type': mime});
                        createReadStream(filePath).pipe(response);
                        console.log(`GET ${url}`);
                    }).catch((e) => {
                        response.writeHead(404, {'Content-Type': 'text/html'});
                        response.end(`<h1>Not found</h1><p>Cannot GET ${url}: ${e}</p>`);
                        console.log(`GET failed ${url}`);
                    });
                }
            });
            server.listen(8080);
            watch(opt);
            break;
        }
        case 'watch':
            watch(opt);
            break;
        case 'build':
            build(opt);
            break;
    }
}

run(process.argv.slice(2));
